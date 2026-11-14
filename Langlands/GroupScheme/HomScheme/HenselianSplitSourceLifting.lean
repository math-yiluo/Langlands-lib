import Langlands.GroupScheme.HomScheme.SmoothSplitSourceRepresentabilityProof
import Langlands.GroupScheme.HomScheme.FibreComparison
import Langlands.CommutativeAlgebra.HenselianSections
import Langlands.GroupScheme.Dynamic.BaseChange

/-! # Exact Henselian lifting from a split torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.HomScheme

/-- Removing identity pullbacks commutes with evaluation on any test scheme. -/
theorem evaluate_identityBase {S : Scheme.{u}} {H G : GroupScheme S}
    (j : RelativeHom H G (Over.mk (𝟙 S))) (T : Over S) :
    evaluate (show T ⟶ Over.mk (𝟙 S) from Over.homMk T.hom (by simp)) j =
      (baseChange T.hom).map
        ((baseChangeIdIso H).inv ≫ j ≫ (baseChangeIdIso G).hom) := by
  apply relativeHom_ext
  rw [evaluate_fst]
  have hproj :
      baseChangeProj H
          (show T ⟶ Over.mk (𝟙 S) from Over.homMk T.hom (by simp)) =
        pullback.fst H.X.hom T.hom ≫ (baseChangeIdIso H).inv.hom.hom.left := by
    apply (cancel_mono (baseChangeIdIso H).hom.hom.hom.left).mp
    simp only [baseChangeIdIso_hom_left, Category.assoc]
    have h :=
      congrArg (fun f => f.hom.hom.left) (baseChangeIdIso H).inv_hom_id
    change (baseChangeIdIso H).inv.hom.hom.left ≫
        pullback.fst H.X.hom (𝟙 S) = 𝟙 _ at h
    rw [h, Category.comp_id]
    exact baseChangeProj_fst H
      (show T ⟶ Over.mk (𝟙 S) from Over.homMk T.hom (by simp))
  rw [hproj]
  change _ =
    ((Over.pullback T.hom).map
      ((baseChangeIdIso H).inv.hom.hom ≫ j.hom.hom ≫
        (baseChangeIdIso G).hom.hom.hom)).left ≫
      pullback.fst G.X.hom T.hom
  simp only [Over.pullback_map_left, pullback.lift_fst,
    Over.comp_left, baseChangeIdIso_hom_left, Category.assoc]
  rfl

/-- Every prescribed homomorphism from the residue fibre of a split torus
to the residue fibre of a smooth affine group lifts over the Henselian base. -/
theorem exists_hom_baseChange_eq
    {R k : Type u} [CommRing R] [HenselianLocalRing R]
    [Field k] [Algebra R k] (hk : Function.Surjective (algebraMap R k))
    (H G : GroupScheme (Spec (CommRingCat.of R)))
    (hH : IsSplitTorus H) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (j₀ : (baseChange (Spec.algebraMap R k)).obj H ⟶
      (baseChange (Spec.algebraMap R k)).obj G) :
    ∃ j : H ⟶ G, (baseChange (Spec.algebraMap R k)).map j = j₀ := by
  let c := Spec.algebraMap R k
  obtain ⟨M, i, hi, hM⟩ := smoothSplitSourceRepresentability _ H G hH
  obtain ⟨b, hb⟩ := (hi (Over.mk c)).surjective j₀
  let : Smooth M.hom := hM
  obtain ⟨s, hs, hcs⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective
      hk M.hom b.left (Over.w b)
  let s' : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ M := Over.homMk s hs
  let c' : Over.mk c ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R))) :=
    Over.homMk c (by simp)
  have hcb : c' ≫ s' = b := by
    apply Over.OverMorphism.ext
    exact hcs
  refine ⟨(baseChangeIdIso H).inv ≫ evaluate s' i ≫ (baseChangeIdIso G).hom, ?_⟩
  calc
    _ = evaluate c' (evaluate s' i) :=
      (evaluate_identityBase (evaluate s' i) (Over.mk c)).symm
    _ = evaluate (c' ≫ s') i := (evaluate_comp c' s' i).symm
    _ = j₀ := by rw [hcb]; exact hb

/-- Exact lifting of any prescribed residue cocharacter, with the canonical
multiplicative-group base-change comparison. -/
theorem exists_cocharacter_baseChange_eq
    {R k : Type u} [CommRing R] [HenselianLocalRing R]
    [Field k] [Algebra R k] (hk : Function.Surjective (algebraMap R k))
    (G : GroupScheme (Spec (CommRingCat.of R)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ₀ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶
      (baseChange (Spec.algebraMap R k)).obj G) :
    ∃ χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G,
      Dynamic.baseChangeCocharacter (Spec.algebraMap R k) χ = χ₀ := by
  obtain ⟨χ, hχ⟩ := exists_hom_baseChange_eq hk
    (Gm (Spec (CommRingCat.of R))).toGrp G isSplitTorus_gm
    ((Gm.baseChangeIso (Spec.algebraMap R k)).hom ≫ χ₀)
  refine ⟨χ, ?_⟩
  simp only [Dynamic.baseChangeCocharacter, hχ, Iso.inv_hom_id_assoc]

/-- Exact lifting for all actual split-torus source homomorphisms and
cocharacters over a Henselian local ring. -/
def HenselianSplitSourceLiftingStatement : Prop :=
  ∀ (R k : Type u) [CommRing R] [HenselianLocalRing R]
    [Field k] [Algebra R k],
    Function.Surjective (algebraMap R k) →
    ∀ (H G : GroupScheme (Spec (CommRingCat.of R))),
      IsSplitTorus H → Smooth G.X.hom → IsAffineHom G.X.hom →
      ∀ j₀ : (baseChange (Spec.algebraMap R k)).obj H ⟶
        (baseChange (Spec.algebraMap R k)).obj G,
        ∃ j : H ⟶ G, (baseChange (Spec.algebraMap R k)).map j = j₀

theorem henselianSplitSourceLifting : HenselianSplitSourceLiftingStatement.{u} := by
  intro R k _ _ _ _ hk H G hH _ _
  exact exists_hom_baseChange_eq hk H G hH

end Langlands.GroupScheme.HomScheme
