import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsInnerCocycle
import Langlands.GroupScheme.SimplyConnected.OuterTypeAEndpointWeights
import Langlands.GroupScheme.Dynamic.GeneralLinearOrbit

/-! # Coordinate lines preserved by inner Tits discrepancies -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

open Matrix LaurentPolynomial
open Langlands.LinearAlgebra.SpecialLinearNormalizedCocycle

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
  (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
    (cover K L))
  (S : CommGroupScheme (Spec (CommRingCat.of K))) (f : S.toGrp ⟶ G)
  (χ : Fin (n + 1) → characterLattice S)
  (hdiag : ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K L)
    (s : Z ⟶ S.X),
    (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
      ((E.toFun a).symm (s ≫ f.hom.hom)) : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
      Matrix.diagonal fun i =>
        ((Gm.pointsEquiv _ Z (s ≫ (CommGroupScheme.groupHom (χ i)).hom.hom) : Γ(Z.left, ⊤)ˣ) :
          Γ(Z.left, ⊤)))

include hdiag

/-- Every inner discrepancy representative centralizes the actual diagonal split-torus image. -/
theorem HasInnerDiscrepancy.commutes_diagonal {σ : L ≃ₐ[K] L}
    {X : GeneralLinearGroup (Fin (n + 1)) L} (hX : HasInnerDiscrepancy E σ X)
    (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K L) (s : Z ⟶ S.X) :
    ((X : Matrix (Fin (n + 1)) (Fin (n + 1)) L).map (coefficients a)) *
        (Matrix.diagonal fun i =>
          ((Gm.pointsEquiv _ Z (s ≫ (CommGroupScheme.groupHom (χ i)).hom.hom) : Γ(Z.left, ⊤)ˣ) :
            Γ(Z.left, ⊤))) =
      (Matrix.diagonal fun i =>
          ((Gm.pointsEquiv _ Z (s ≫ (CommGroupScheme.groupHom (χ i)).hom.hom) : Γ(Z.left, ⊤)ˣ) :
            Γ(Z.left, ⊤))) *
        ((X : Matrix (Fin (n + 1)) (Fin (n + 1)) L).map (coefficients a)) := by
  let g := SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
    ((E.toFun a).symm (s ≫ f.hom.hom))
  have hg (b : Z ⟶ cover K L) :
      SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
        ((E.toFun b).symm (s ≫ f.hom.hom)) = g := by
    apply Subtype.ext
    exact (hdiag Z b s).trans (hdiag Z a s).symm
  have h := hX.commutes_of_coordinates E a (s ≫ f.hom.hom) g hg
  have hm := congrArg (fun z : GeneralLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤) =>
    (z : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))) h
  change (X.val.map (coefficients a)) * g.val = g.val * (X.val.map (coefficients a)) at hm
  rw [show g.val = _ from hdiag Z a s] at hm
  exact hm

omit E S f χ hdiag in
/-- The generic Laurent test has its canonical point of the extension-field cover. -/
def laurentCoverPoint :
    GeneralLinear.laurentScheme (algebraBaseMap K L) ⟶ cover K L :=
  GeneralLinear.laurentIncl (algebraBaseMap K L) ≫
    GeneralLinear.polyProj (algebraBaseMap K L)

omit E S f χ hdiag in
/-- The cover coefficients on the Laurent test are constant Laurent polynomials. -/
theorem coefficients_laurentCoverPoint (x : L) :
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial L))).hom
      (coefficients (laurentCoverPoint (K := K) (L := L)) x) = C x := by
  have hc := congrArg (fun z : L →+* Γ((GeneralLinear.laurentScheme
      (algebraBaseMap K L)).left, ⊤) => z x)
    (coefficients_naturality (laurentCoverPoint (K := K) (L := L)) (𝟙 (cover K L)))
  simp only [Category.comp_id, RingHom.comp_apply] at hc
  rw [hc]
  calc
    _ = C ((Scheme.ΓSpecIso (CommRingCat.of L)).hom (coefficients (𝟙 (cover K L)) x)) :=
      GeneralLinear.ΓSpecIso_hom_laurentProj (R := CommRingCat.of K) (A := CommRingCat.of L)
        (f := algebraBaseMap K L) (coefficients (𝟙 (cover K L)) x)
    _ = C x := by
      change C ((Scheme.ΓSpecIso (CommRingCat.of L)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of L)).inv x)) = C x
      rw [Iso.inv_hom_id_apply]

omit E f χ hdiag in
/-- The generic unit followed by a supplied cocharacter of the torus. -/
def genericTorusPoint (ν : cocharacterLattice S) :
    GeneralLinear.laurentScheme (algebraBaseMap K L) ⟶ S.X :=
  (Gm.pointsEquiv _ _).symm (GeneralLinear.laurentUnit (algebraBaseMap K L)) ≫
    (CommGroupScheme.groupHom ν).hom.hom

omit E f χ hdiag in
/-- Evaluating a character at the generic cocharacter gives its integer Laurent weight. -/
theorem genericTorusPoint_weight (ν : cocharacterLattice S) (ψ : characterLattice S) :
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial L))).hom
      ((Gm.pointsEquiv _ _ (genericTorusPoint S ν ≫
        (CommGroupScheme.groupHom ψ).hom.hom) :
          Γ((GeneralLinear.laurentScheme (algebraBaseMap K L)).left, ⊤)ˣ) :
          Γ((GeneralLinear.laurentScheme (algebraBaseMap K L)).left, ⊤)) =
      T (latticePairing S ψ ν) := by
  let t := (Gm.pointsEquiv _ _).symm (GeneralLinear.laurentUnit (algebraBaseMap K L))
  have hpair : ν ≫ ψ = (gmEndEquiv K).symm (latticePairing S ψ ν) :=
    ((gmEndEquiv K).symm_apply_apply (ν ≫ ψ)).symm
  have heval : genericTorusPoint S ν ≫ (CommGroupScheme.groupHom ψ).hom.hom =
      t ^ (latticePairing S ψ ν) := by
    change (t ≫ (CommGroupScheme.groupHom ν).hom.hom) ≫ _ = _
    rw [← comp_groupHom_comp, hpair, gmEndEquiv_symm_comp]
  rw [heval, map_zpow, MulEquiv.apply_symm_apply]
  exact GeneralLinear.ΓSpecIso_hom_laurentUnit_zpow (algebraBaseMap K L) _

/-- Inner representatives have zero entries between different cocharacter weights. -/
theorem HasInnerDiscrepancy.entry_eq_zero_of_weight_ne {σ : L ≃ₐ[K] L}
    {X : GeneralLinearGroup (Fin (n + 1)) L} (hX : HasInnerDiscrepancy E σ X)
    (ν : cocharacterLattice S) (i j : Fin (n + 1))
    (hij : latticePairing S (χ i) ν ≠ latticePairing S (χ j) ν) : X i j = 0 := by
  have hm := hX.commutes_diagonal E S f χ hdiag _ (laurentCoverPoint (K := K) (L := L))
    (genericTorusPoint S ν)
  have h := congrArg (fun z : Matrix (Fin (n + 1)) (Fin (n + 1))
      Γ((GeneralLinear.laurentScheme (algebraBaseMap K L)).left, ⊤) =>
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial L))).hom (z i j)) hm
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, map_mul] at h
  rw [coefficients_laurentCoverPoint (K := K) (L := L),
    genericTorusPoint_weight (K := K) (L := L) S ν (χ j),
    genericTorusPoint_weight (K := K) (L := L) S ν (χ i)] at h
  by_contra hXij
  have hs : (AddMonoidAlgebra.single (latticePairing S (χ j) ν) (X i j) : LaurentPolynomial L) =
      AddMonoidAlgebra.single (latticePairing S (χ i) ν) (X i j) := by
    rw [single_eq_C_mul_T, single_eq_C_mul_T]
    exact h.trans (mul_comm _ _)
  exact hij ((AddMonoidAlgebra.single_left_inj hXij).mp hs).symm

/-- A weight occurring in just one coordinate gives a preserved coordinate line. -/
theorem HasInnerDiscrepancy.preservesCoordinate {σ : L ≃ₐ[K] L}
    {X : GeneralLinearGroup (Fin (n + 1)) L} (hX : HasInnerDiscrepancy E σ X)
    (ν : cocharacterLattice S) (p : Fin (n + 1))
    (hp : ∀ i, i ≠ p → latticePairing S (χ i) ν ≠ latticePairing S (χ p) ν) :
    PreservesCoordinate p X := by
  intro i hi
  exact hX.entry_eq_zero_of_weight_ne E S f χ hdiag ν i p (hp i hi)


omit hdiag

section TitsEndpoints

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) (e : d.Vertex ≃ Fin n)
  (ψ : Fin (n + 1) → characterLattice d.splitTorus)
  (hroot : ∀ i : Fin n, d.rootRestriction (e.symm i).val = ψ i.castSucc - ψ i.succ)
  (hψ : ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K L)
    (s : Z ⟶ d.splitTorus.X),
    (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
      ((E.toFun a).symm (s ≫ d.splitInclusion.hom.hom)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
      Matrix.diagonal fun i =>
        ((Gm.pointsEquiv _ Z (s ≫ (CommGroupScheme.groupHom (ψ i)).hom.hom) : Γ(Z.left, ⊤)ˣ) :
          Γ(Z.left, ⊤)))

include hroot hψ

/-- A distinguished first vertex forces inner discrepancy matrices to preserve the first line. -/
theorem HasInnerDiscrepancy.preserves_first {σ : L ≃ₐ[K] L}
    {X : GeneralLinearGroup (Fin (n + 1)) L} (hX : HasInnerDiscrepancy E σ X)
    (hn : 0 < n) (hfirst : e.symm ⟨0, hn⟩ ∈ d.distinguishedVertices) :
    PreservesCoordinate 0 X := by
  apply hX.preservesCoordinate E d.splitTorus d.splitInclusion ψ hψ d.positiveCocharacter 0
  intro i hi
  exact (d.first_weightValues_gt e ψ hroot hn hfirst i hi).ne

/-- A distinguished last vertex forces inner discrepancy matrices to preserve the last line. -/
theorem HasInnerDiscrepancy.preserves_last {σ : L ≃ₐ[K] L}
    {X : GeneralLinearGroup (Fin (n + 1)) L} (hX : HasInnerDiscrepancy E σ X)
    (hn : 0 < n) (hlast : e.symm ⟨n - 1, by omega⟩ ∈ d.distinguishedVertices) :
    PreservesCoordinate (Fin.last n) X := by
  apply hX.preservesCoordinate E d.splitTorus d.splitInclusion ψ hψ
    d.positiveCocharacter (Fin.last n)
  intro i hi
  exact (d.last_weightValues_lt e ψ hroot hn hlast i hi).ne'

/-- Inner representatives and a distinguished first vertex give a normalized,
honest matrix cocycle representing the same all-test discrepancies. -/
theorem exists_normalized_inner_cocycle (H : Subgroup (L ≃ₐ[K] L))
    (x : H → GeneralLinearGroup (Fin (n + 1)) L)
    (hx : ∀ σ, HasInnerDiscrepancy E σ.val (x σ))
    (hn : 0 < n) (hfirst : e.symm ⟨0, hn⟩ ∈ d.distinguishedVertices) :
    ∃ y : H → GeneralLinearGroup (Fin (n + 1)) L,
      y 1 = 1 ∧
      (∀ σ τ, y (σ * τ) = y σ * GeneralLinearGroup.map σ.val.toRingHom (y τ)) ∧
      (∀ σ, HasInnerDiscrepancy E σ.val (y σ)) ∧
      ∀ σ i, y σ i 0 = if i = 0 then 1 else 0 := by
  have hp (σ : H) := (hx σ).preserves_first E d e ψ hroot hψ hn hfirst
  let y : H → GeneralLinearGroup (Fin (n + 1)) L := fun σ => normalize (x σ) 0 (hp σ)
  refine ⟨y, normalized_identity E (hx 1) 0 (hp 1), ?_, ?_, ?_⟩
  · exact normalized_cocycle E H x hx 0 hp
  · intro σ
    exact (hx σ).normalize E 0 (hp σ)
  · intro σ i
    exact normalize_column (x σ) 0 (hp σ) i

end TitsEndpoints

end Langlands.GroupScheme.SpecialLinearTitsCocycle
