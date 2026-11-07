import Langlands.GroupScheme.Reductive.LocalSplitCellIsomorphism
import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.Reductive.LocalSplitBigCellProof

/-! # Point-group isomorphisms over field points from isomorphisms of field fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))} (K : Type u) [Field K] [Algebra R K]

local notation "bK" => algebraBaseMap R K
local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap R K)) G
local notation "H_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap R K)) H

/-- An isomorphism of the field fibres that matches the base-changed tori, the base-changed
simple-root parametrizations and their negative-root points at `-1` gives an isomorphism of
the point groups over `fieldPoint R K` that matches the tori and the whole Weyl families. -/
theorem exists_fieldPointsEquiv {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} (Φ : G_K ≅ H_K)
    (hΦ : splitTorus.baseChangeHom (K := K) G I i ≫ Φ.hom =
      splitTorus.baseChangeHom (K := K) H I i')
    (P : RootDatum J (I → ℤ) (I → ℤ)) {b : P.Base} (W : ∀ α, SimpleWord P b α)
    {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)} {uK : J → (Ga K ⟶ G_K)}
    {uK' : J → (Ga K ⟶ H_K)}
    (hpt : ∀ a (T : Over (Spec (CommRingCat.of K))) (c : Γ(T.left, ⊤)),
      GroupScheme.baseChangePointsEquiv bK G T (rootPoint (uK a) T c) =
        rootPoint (u a) ((Over.map bK).obj T) c)
    (hpt' : ∀ a (T : Over (Spec (CommRingCat.of K))) (c : Γ(T.left, ⊤)),
      GroupScheme.baseChangePointsEquiv bK H T (rootPoint (uK' a) T c) =
        rootPoint (u' a) ((Over.map bK).obj T) c)
    (hs : ∀ a ∈ b.support, uK a ≫ Φ.hom = uK' a)
    (hneg : ∀ a ∈ b.support,
      rootPoint (uK (P.reflectionPerm a a)) (𝟙_ _) (-1) ≫ Φ.hom.hom.hom =
        rootPoint (uK' (P.reflectionPerm a a)) (𝟙_ _) (-1)) :
    ∃ Ψ : (fieldPoint R K ⟶ G.X) ≃* (fieldPoint R K ⟶ H.X),
      (∀ t : fieldPoint R K ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
        Ψ (t ≫ i.hom.hom) = t ≫ i'.hom.hom) ∧
      ∀ α c, Ψ (rootPoint (weylFamily P W u α) _ c) = rootPoint (weylFamily P W u' α) _ c := by
  let pt := 𝟙_ (Over (Spec (CommRingCat.of K)))
  let EG := GroupScheme.baseChangePointsEquiv bK G pt
  let EH := GroupScheme.baseChangePointsEquiv bK H pt
  let Ψ : (fieldPoint R K ⟶ G.X) ≃* (fieldPoint R K ⟶ H.X) :=
    (EG.symm.trans (GroupScheme.isoPointsEquiv Φ pt)).trans EH
  have hΨ : ∀ y, Ψ (EG y) = EH (y ≫ Φ.hom.hom.hom) := by
    intro y
    change EH (EG.symm (EG y) ≫ Φ.hom.hom.hom) = _
    rw [MulEquiv.symm_apply_apply]
  have hroot : ∀ a, uK a ≫ Φ.hom = uK' a → ∀ c,
      Ψ (rootPoint (u a) (fieldPoint R K) c) = rootPoint (u' a) (fieldPoint R K) c := by
    intro a ha c
    rw [← hpt a pt c, hΨ, ← rootPoint_comp, ha, hpt']
  refine ⟨Ψ, fun t => ?_, fun α c => ?_⟩
  · let ET := GroupScheme.baseChangePointsEquiv bK (splitTorus (Spec (CommRingCat.of R)) I) pt
    obtain ⟨t₀, rfl⟩ := ET.surjective t
    have hi : (GroupScheme.baseChange bK).map i =
        (splitTorus.baseChangeIso bK I).hom ≫ splitTorus.baseChangeHom (K := K) G I i := by
      rw [splitTorus.baseChangeHom, Iso.hom_inv_id_assoc]
    have hi' : (GroupScheme.baseChange bK).map i' =
        (splitTorus.baseChangeIso bK I).hom ≫ splitTorus.baseChangeHom (K := K) H I i' := by
      rw [splitTorus.baseChangeHom, Iso.hom_inv_id_assoc]
    rw [← GroupScheme.baseChangePointsEquiv_comp, ← GroupScheme.baseChangePointsEquiv_comp, hΨ,
      Category.assoc, ← Grp.comp_hom_hom, hi, hi', Category.assoc, hΦ]
  · exact map_rootPoint_weylFamily W Ψ.toMonoidHom (fun a ha c => hroot a (hs a ha) c)
      (fun a ha => by
        change Ψ _ = _
        rw [← hpt _ pt (-1), hΨ, hneg a ha, hpt']) α c

section WeylBaseChange

open LocalSplitBigCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} (K : Type u) [Field K] [Algebra R K]

/-- The base change to a field of a Weyl point built from two root maps is the Weyl point of
the base-changed root maps, with the same exponent automorphism. -/
theorem IsWeylPoint.baseChange {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {u v : Ga R ⟶ G} {f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)} (h : IsWeylPoint i (weylPoint u v) f) :
    IsWeylPoint (splitTorus.baseChangeHom (K := K) G I i)
      (weylPoint (baseChangeRoot K u) (baseChangeRoot K v)) f := by
  intro Z t
  let E := GroupScheme.baseChangePointsEquiv (algebraBaseMap R K) G Z
  let ET := GroupScheme.baseChangePointsEquiv (algebraBaseMap R K) (splitTorus _ I) Z
  let Z' := (Over.map (algebraBaseMap R K)).obj Z
  apply E.injective
  have hN : E (toUnit Z ≫ weylPoint (baseChangeRoot K u) (baseChangeRoot K v)) =
      toUnit Z' ≫ weylPoint u v := by
    rw [toUnit_comp_eq_constantPoint, constantPoint_weylPoint, map_mul, map_mul,
      baseChangePointsEquiv_rootPoint, baseChangePointsEquiv_rootPoint,
      toUnit_comp_eq_constantPoint, constantPoint_weylPoint]
  have hexp : (splitTorus.exponentIso (Spec (CommRingCat.of K)) I f).hom ≫
      (splitTorus.baseChangeIso (algebraBaseMap R K) I).inv =
        (splitTorus.baseChangeIso (algebraBaseMap R K) I).inv ≫
          (GroupScheme.baseChange (algebraBaseMap R K)).map
            (splitTorus.exponentIso (Spec (CommRingCat.of R)) I f).hom := by
    rw [Iso.eq_inv_comp, ← Category.assoc,
      splitTorus.exponentIso_baseChange (Spec (CommRingCat.of R)) I (algebraBaseMap R K) f,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have ht : ET ((t ≫ (splitTorus.exponentIso _ I f).hom.hom.hom) ≫
      (splitTorus.baseChangeIso (algebraBaseMap R K) I).inv.hom.hom) =
        ET (t ≫ (splitTorus.baseChangeIso (algebraBaseMap R K) I).inv.hom.hom) ≫
          (splitTorus.exponentIso (Spec (CommRingCat.of R)) I f).hom.hom.hom := by
    rw [← GroupScheme.baseChangePointsEquiv_comp, Category.assoc, Category.assoc,
      ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hexp]
  rw [map_mul, map_mul, map_inv, hN, baseChangePointsEquiv_torus, ← Category.assoc,
    baseChangePointsEquiv_torus, ht, h Z' _, Category.assoc]

end WeylBaseChange

end Langlands.GroupScheme.LocalSplitCell
