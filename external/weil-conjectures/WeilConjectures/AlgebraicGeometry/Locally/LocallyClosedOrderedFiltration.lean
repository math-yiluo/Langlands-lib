/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
public import Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedCoefficientExtensionComposition
import WeilConjectures.ConstructibleSheaf.Devissage

/-! # Filtration of a locally closed extension along prescribed ordered strata

## Implementation details

The filtration of `L` comes from the open prefixes `U_b` of the stratification: the images of
`U_b! U_b* L → L` have successive quotients `t_b! t_b* L` by open-closed recollement. The exact
extension `a_!` carries this filtration to `a_! L`, and transitivity of locally closed extension
identifies `a_! t_b!` with `(t_b ≫ a)_!`. No constructibility of the coefficients is needed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

-- Keep the transport through chosen representatives in an abstract abelian category.
private theorem exact_filtration_transport
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (L : C) (n : ℕ) (G : Fin (n + 1) → Subobject L)
    (h0 : G 0 = ⊥) (htop : G (Fin.last n) = ⊤)
    (h : ∀ b : Fin n, G b.castSucc ≤ G b.succ) :
    ∃ F : Fin (n + 1) → Subobject (T.obj L),
      F 0 = ⊥ ∧ F (Fin.last n) = ⊤ ∧
      ∃ hF : ∀ b : Fin n, F b.castSucc ≤ F b.succ,
        ∀ b : Fin n, Nonempty (cokernel (Subobject.ofLE _ _ (hF b)) ≅
          T.obj (cokernel (Subobject.ofLE _ _ (h b)))) := by
  let F : Fin (n + 1) → Subobject (T.obj L) := fun b ↦ Subobject.mk (T.map (G b).arrow)
  have hF (b : Fin n) : F b.castSucc ≤ F b.succ :=
    Subobject.mk_le_mk_of_comm (T.map (Subobject.ofLE _ _ (h b))) (by
      rw [← T.map_comp, Subobject.ofLE_arrow])
  refine ⟨F, ?_, ?_, hF, fun b ↦ ?_⟩
  · change Subobject.mk (T.map (G 0).arrow) = ⊥
    rw [h0]
    apply Subobject.mk_eq_bot_iff_zero.mpr
    rw [Subobject.bot_arrow, T.map_zero]
  · change Subobject.mk (T.map (G (Fin.last n)).arrow) = ⊤
    rw [htop]
    exact Subobject.mk_eq_top_of_isIso _
  · exact ⟨Subobject.cokernelOfLEMkIso _ _ (Iso.refl _)
      (T.map (Subobject.ofLE _ _ (h b))) (by simp [← T.map_comp]) (hF b) ≪≫
        (PreservesCokernel.iso T _).symm⟩

attribute [local irreducible] coefficientHeartLocallyClosedExtension

/-- Extension by zero sends the ordered stratum filtration to a filtration of its
specified extension, with quotients extended along the composite immersions. -/
theorem exists_locallyClosedOrderedFiltration
    (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B] {S X : Scheme.{u}}
    [IsNoetherian S] [IsNoetherian X] (a : S ⟶ X) [IsImmersion a]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj B S))
    (R : S.FiniteLocallyClosedStratification)
    (hR : ∀ b : Fin (R.n + 1),
      IsOpen (⋃ i : Fin R.n, ⋃ (_ : i.val < b.val), R.stratum i)) :
    ∃ F : Fin (R.n + 1) →
        Subobject ((coefficientHeartLocallyClosedExtension B a inferInstance).obj L),
      F 0 = ⊥ ∧ F (Fin.last R.n) = ⊤ ∧
      ∃ h : ∀ b : Fin R.n, F b.castSucc ≤ F b.succ,
        ∀ b : Fin R.n,
          letI : IsImmersion (R.immersion b) := R.isImmersion b
          Nonempty (cokernel (Subobject.ofLE (F b.castSucc) (F b.succ) (h b)) ≅
            (coefficientHeartLocallyClosedExtension B (R.immersion b ≫ a)
              inferInstance).obj ((CondensedRing.upperStar B (R.immersion b)).obj L)) := by
  classical
  let V : Fin (R.n + 1) → S.Opens := fun b ↦
    ⟨⋃ i : Fin R.n, ⋃ (_ : i.val < b.val), R.stratum i, hR b⟩
  obtain ⟨_, h0, htop, h, hq⟩ := openPrefix_filtration B S L R V (fun _ ↦ rfl)
  let T := coefficientHeartLocallyClosedExtension B a inferInstance
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hlim, hcol, hadd, _⟩ :=
    (coefficientHeart_locallyClosedExtension B X).2 S a inferInstance
  have : PreservesFiniteLimits T := hlim
  have : PreservesFiniteColimits T := hcol
  have : T.Additive := hadd
  obtain ⟨F, hF0, hFtop, hF, he⟩ := exact_filtration_transport T L R.n
    (fun b ↦ coefficientHeartFiltrationStep B L (V b)) h0 htop h
  refine ⟨F, hF0, hFtop, hF, fun b ↦ ?_⟩
  have : IsImmersion (R.immersion b) := R.isImmersion b
  obtain ⟨e⟩ := he b
  obtain ⟨eq⟩ := hq b
  obtain ⟨ec⟩ := locallyClosedCoefficientExtension_composition B a (R.immersion b)
    ((CondensedRing.upperStar B (R.immersion b)).obj L)
  exact ⟨e ≪≫ T.mapIso eq ≪≫ ec⟩

end AlgebraicGeometry.ProEtale
