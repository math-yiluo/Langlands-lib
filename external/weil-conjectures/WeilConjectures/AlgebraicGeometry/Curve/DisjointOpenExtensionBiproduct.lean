/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.SixFunctors.OpenClosed.Conservative
import WeilConjectures.SixFunctors.OpenClosed.Vanishing

/-!
# Extension by zero from disjoint opens as a finite biproduct

Source: Stacks Project, Theorem 03SC, proof, fourth paragraph; Lemma 0A5C
(blueprint: lem-pbc-t2-disjoint-open-extension-biproduct).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Etale

/-- Extension from a finite disjoint union of opens is the biproduct of the extensions
from its members. No curve, torsion or constructibility assumption is needed.
Source: Stacks Project, Theorem 03SC, proof, fourth paragraph; Lemma 0A5C
(blueprint: lem-pbc-t2-disjoint-open-extension-biproduct).

Proof: Write W for the union and i_a : U_a → W for the inclusions. On W form the
map φ : ⨁ a, i_a! i_a* (F|W) → F|W given by the counits. The i_a are jointly
surjective, so it suffices to check that i_a* φ is invertible for every a. For b ≠ a,
the ranges of i_a and i_b are disjoint, hence i_a* i_b! is zero. The biproduct
identities then show that i_a* of the a-th inclusion is an isomorphism: its inverse
is i_a* of the a-th projection, since every other term in the total identity
vanishes. Its composite with i_a* φ is the restricted a-th counit, an isomorphism
by the adjunction triangle identity and the invertible unit of i_a! ⊣ i_a*.
Thus i_a* φ and consequently φ are isomorphisms. Apply j_W! to φ, commute that
additive functor with the finite biproduct, and identify j_W! i_a! with j_a! and
i_a* j_W* with j_a* using the composition isomorphisms. Invert the resulting
isomorphism to obtain the stated orientation. When n = 0 the covering criterion
is vacuous because W is empty; the same proof applies. -/
theorem disjointOpenExtension_biproduct_iso (Λ : Type (u + 1)) [CommRing Λ]
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (n : ℕ) (U : Fin n → X.Opens)
    (hU : Pairwise (fun a b ↦ Disjoint (U a : Set X) (U b))) :
    Nonempty
      ((((⨆ a, U a).ι)_!open[ModuleCat.{u + 1} Λ].obj
          (((⨆ a, U a).ι)^*[ModuleCat.{u + 1} Λ].obj F)) ≅
        ⨁ (fun a ↦ (((U a).ι)_!open[ModuleCat.{u + 1} Λ].obj
          (((U a).ι)^*[ModuleCat.{u + 1} Λ].obj F)))) := by
  classical
  let A := ModuleCat.{u + 1} Λ
  let W : X.Opens := ⨆ a, U a
  let i (a : Fin n) : (U a).toScheme ⟶ W.toScheme := X.homOfLE (le_iSup U a)
  let FW := (W.ι)^*[A].obj F
  let G (a : Fin n) := (i a)_!open[A].obj ((i a)^*[A].obj FW)
  let ε (a : Fin n) : G a ⟶ FW :=
    (openImmersionLowerShriekUpperStarAdjunction A (i a)).counit.app FW
  let φ : ⨁ G ⟶ FW := biproduct.desc ε
  have hφ : IsIso φ := by
    refine isIso_of_isIso_upperStar_map_of_jointlySurjective A
      (fun a : ULift.{u} (Fin n) ↦ i a.down) ?_ φ ?_
    · intro x
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
      exact ⟨⟨a⟩, ⟨x.1, ha⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
    · intro a
      let a := a.down
      let P := (i a)^*[A]
      have hz (b : Fin n) (hba : b ≠ a) : IsZero (P.obj (G b)) := by
        apply isZero_upperStar_openImmersionLowerShriek_of_disjoint_range A (i b) (i a)
        rw [Set.disjoint_left]
        rintro x ⟨y, rfl⟩ ⟨z, hz⟩
        have hy : y.1 ∈ (U b : Set X) := y.2
        have hz' : z.1 ∈ (U a : Set X) := z.2
        have heq : y.1 = z.1 := by
          simpa [i, Scheme.homOfLE_apply] using congrArg Subtype.val hz.symm
        exact (hU hba).ne_of_mem hy hz' heq
      have hι : IsIso (P.map (biproduct.ι G a)) := by
        refine ⟨P.map (biproduct.π G a), ?_, ?_⟩
        · rw [← P.map_comp, biproduct.ι_π_self, P.map_id]
        · rw [← P.map_comp, ← P.map_id, ← IsBilimit.total (biproduct.isBilimit G),
            P.map_sum, Finset.sum_eq_single a (fun b _ hba ↦ ?_) (by simp)]
          rw [P.map_comp, (hz b hba).eq_zero_of_tgt (P.map (biproduct.π G b)), zero_comp]
      have hε : IsIso (P.map (ε a)) := by
        dsimp [P, ε]
        infer_instance
      have : IsIso (P.map (biproduct.ι G a) ≫ P.map φ) := by
        rw [← P.map_comp, biproduct.ι_desc]
        exact hε
      exact IsIso.of_isIso_comp_left (P.map (biproduct.ι G a)) (P.map φ)
  let e (a : Fin n) :
      (W.ι)_!open[A].obj (G a) ≅
        (((U a).ι)_!open[A].obj (((U a).ι)^*[A].obj F)) := by
    have hi : i a ≫ W.ι = (U a).ι := Scheme.homOfLE_ι _ _
    let e₁ := ((openImmersionLowerShriekComp A (i a) W.ι).app
      ((i a)^*[A].obj FW)).symm
    let e₂ := ((i a ≫ W.ι)_!open[A]).mapIso
      ((upperStarComp A (i a) W.ι).app F).symm
    exact e₁ ≪≫ e₂ ≪≫ eqToIso (by simp only [hi])
  exact ⟨((W.ι)_!open[A]).mapIso (asIso φ).symm ≪≫
    ((W.ι)_!open[A]).mapBiproduct G ≪≫ biproduct.mapIso e⟩

end AlgebraicGeometry.Etale

