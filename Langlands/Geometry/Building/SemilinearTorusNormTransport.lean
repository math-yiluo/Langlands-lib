import Langlands.GroupScheme.Rational.RingEquivBaseChange
import Langlands.Geometry.Building.KPCharacterValuationExtension
import Langlands.GroupScheme.GaloisPointTowerBaseChange
import Langlands.GroupScheme.Absolute.ParabolicBorelFactorization

/-! # Torus norms in a square of isomorphic coefficient fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building

section FieldIso

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- A surjective coefficient map makes every coefficient automorphism trivial. -/
theorem algebraAut_subsingleton_of_surjective
    (h : Function.Surjective (algebraMap k K)) : Subsingleton (K ≃ₐ[k] K) :=
  ⟨fun σ τ => AlgEquiv.ext fun x => by
    obtain ⟨a, rfl⟩ := h x
    rw [σ.commutes, τ.commutes]⟩

variable [FiniteDimensional k K] [IsGalois k K]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

/-- In degree one the descended norm is injective. -/
theorem rationalNorm_injective_of_surjective
    (h : Function.Surjective (algebraMap k K)) :
    Function.Injective (rationalNorm k K T) := by
  have := algebraAut_subsingleton_of_surjective k K h
  have hn (x : rationalPoints (baseChanged k K T.toGrp)) :
      rationalExtend k K T.toGrp (rationalNorm k K T x) = x := by
    rw [rationalExtend_norm]
    exact (Fintype.prod_subsingleton _ (1 : K ≃ₐ[k] K)).trans
      (rationalConjugate_one k K T.toGrp x)
  intro x y hxy
  exact (hn x).symm.trans ((congrArg (rationalExtend k K T.toGrp) hxy).trans (hn y))

/-- The norm after extension is the identity in degree one. -/
theorem rationalNorm_extend_of_finrank_one
    (h : Module.finrank k K = 1) (x : rationalPoints T.toGrp) :
    rationalNorm k K T (rationalExtend k K T.toGrp x) = x :=
  (rationalNorm_extend k K T x).trans (by rw [h, pow_one])

end FieldIso

private theorem rationalPoints_iso_inv_hom {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    (e : G ≅ H) (x : rationalPoints H) :
    rationalPoints.map e.hom (rationalPoints.map e.inv x) = x := by
  change (x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x
  rw [Category.assoc, ← Grp.comp_hom_hom, e.inv_hom_id]
  rfl

private theorem mulEquiv_symm_mem_characterValuationKernel
    {k : Type u} [Field k] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation k Γ) {G H : GroupScheme (Spec (CommRingCat.of k))}
    (e : G ≅ H) (q : rationalPoints G ≃* rationalPoints H)
    (hq : ∀ x, q x = rationalPoints.map e.hom x)
    (z : rationalPoints H) (hz : z ∈ characterValuationKernel v H) :
    q.symm z ∈ characterValuationKernel v G := by
  have h : q.symm z = rationalPoints.map e.inv z := by
    apply q.injective
    rw [q.apply_symm_apply, hq, rationalPoints_iso_inv_hom]
  rw [h]
  exact map_characterValuationKernel_le v e.inv ⟨z, hz, rfl⟩

private theorem subgroup_map_le_of_square
    {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]
    (S : Subgroup A) (U : Subgroup C)
    (N : A →* B) (f : B →* D) (Q : A →* C) (N' : C →* D)
    (h : ∀ x, N' (Q x) = f (N x))
    (hQ : ∀ x, x ∈ S → Q x ∈ U) :
    (S.map N).map f ≤ U.map N' := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact ⟨Q x, hQ x hx, h x⟩

private theorem norm_square_of_injective
    {A B C D E F : Type*}
    (nAB : B → A) (nAC : C → A) (nAD : D → A)
    (nBE : E → B) (nCF : F → C)
    (eAB : A → B) (eCF : C → F) (qE : E ≃ D) (qF : F ≃ D)
    (hi : Function.Injective nAB)
    (hE : ∀ x, nAB (nBE x) = nAD (qE x))
    (hF : ∀ x, nAC (nCF x) = nAD (qF x))
    (hAB : ∀ x, nAB (eAB x) = x)
    (hCF : ∀ x, nCF (eCF x) = x) (x : C) :
    nBE (qE.symm (qF (eCF x))) = eAB (nAC x) := by
  apply hi
  calc
    _ = nAD (qE (qE.symm (qF (eCF x)))) := hE _
    _ = nAD (qF (eCF x)) := congrArg nAD (qE.apply_symm_apply _)
    _ = nAC (nCF (eCF x)) := (hF _).symm
    _ = nAC x := congrArg nAC (hCF x)
    _ = _ := (hAB _).symm

section CommTower

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

private instance commBaseChangedAffine [IsAffine T.X.left] :
    IsAffine ((CommGroupScheme.baseChange (baseMap k L)).obj T).X.left := by
  change IsAffine (pullback T.X.hom (baseMap k L))
  infer_instance

/-- The tower comparison as successive coefficient-point equivalences. -/
def commTowerRationalEquiv :
    rationalPoints ((CommGroupScheme.baseChange (baseMap L M)).obj
      ((CommGroupScheme.baseChange (baseMap k L)).obj T)).toGrp ≃*
        rationalPoints ((CommGroupScheme.baseChange (baseMap k M)).obj T).toGrp :=
  ((baseChangeCoeffEquiv L M
      ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp).trans
    (coefficientBaseChangeEquiv k L M T.toGrp)).trans
      (baseChangeCoeffEquiv k M T.toGrp).symm

private theorem baseChangeCoeffEquiv_commTowerRationalEquiv
    (y : rationalPoints ((CommGroupScheme.baseChange (baseMap L M)).obj
      ((CommGroupScheme.baseChange (baseMap k L)).obj T)).toGrp) :
    baseChangeCoeffEquiv k M T.toGrp (commTowerRationalEquiv k L M T y) =
      coefficientBaseChangeEquiv k L M T.toGrp
        (baseChangeCoeffEquiv L M
          ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp y) :=
  (baseChangeCoeffEquiv k M T.toGrp).apply_symm_apply _

/-- Its point action agrees with the scheme-theoretic tower comparison. -/
theorem commTowerRationalEquiv_apply
    (y : rationalPoints ((CommGroupScheme.baseChange (baseMap L M)).obj
      ((CommGroupScheme.baseChange (baseMap k L)).obj T)).toGrp) :
    commTowerRationalEquiv k L M T y =
      rationalPoints.map (towerBaseChangeIso k L M T.toGrp).hom y := by
  apply (baseChangeCoeffEquiv k M T.toGrp).injective
  exact (baseChangeCoeffEquiv_commTowerRationalEquiv k L M T y).trans
    (baseChangeCoeffEquiv_towerBaseChangeIso k L M T.toGrp y).symm

variable [FiniteDimensional L M] [IsGalois L M] [IsAffine T.X.left]

private theorem relativeRationalNorm_commTowerRationalEquiv
    (y : rationalPoints ((CommGroupScheme.baseChange (baseMap L M)).obj
      ((CommGroupScheme.baseChange (baseMap k L)).obj T)).toGrp) :
    relativeRationalNorm k L M T (commTowerRationalEquiv k L M T y) =
      rationalNorm L M ((CommGroupScheme.baseChange (baseMap k L)).obj T) y :=
  (congrArg (relativeRationalNorm k L M T)
    (commTowerRationalEquiv_apply k L M T y)).trans
      (relativeRationalNorm_towerBaseChangeIso k L M T y)

private theorem rationalNorm_commTowerRationalEquiv
    [FiniteDimensional k L] [FiniteDimensional k M]
    [IsGalois k L] [IsGalois k M]
    (y : rationalPoints ((CommGroupScheme.baseChange (baseMap L M)).obj
      ((CommGroupScheme.baseChange (baseMap k L)).obj T)).toGrp) :
    rationalNorm k L T
        (rationalNorm L M ((CommGroupScheme.baseChange (baseMap k L)).obj T) y) =
      rationalNorm k M T (commTowerRationalEquiv k L M T y) :=
  (congrArg (rationalNorm k L T)
    (relativeRationalNorm_commTowerRationalEquiv k L M T y)).symm.trans
      (rationalNorm_relativeRationalNorm k L M T _)

end CommTower

section Square

variable (k K L M : Type u) [Field k] [Field K] [Field L] [Field M]
  [Algebra k K] [Algebra k L] [Algebra k M] [Algebra K M] [Algebra L M]
  [IsScalarTower k K M] [IsScalarTower k L M]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- Transport between the two iterated base changes in a field square. -/
def squareRationalExtend :
    rationalPoints ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp →*
      rationalPoints ((CommGroupScheme.baseChange (baseMap K M)).obj
        ((CommGroupScheme.baseChange (baseMap k K)).obj T)).toGrp :=
  (commTowerRationalEquiv k K M T).symm.toMonoidHom.comp
    ((commTowerRationalEquiv k L M T).toMonoidHom.comp
      (rationalExtend L M ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp))

variable [FiniteDimensional k K] [FiniteDimensional k L] [FiniteDimensional k M]
  [FiniteDimensional K M] [FiniteDimensional L M]
  [IsGalois k K] [IsGalois k L] [IsGalois k M]
  [IsGalois K M] [IsGalois L M] [IsAffine T.X.left]

/-- Norms commute with extension through the isomorphic sides of a field square. -/
theorem rationalNorm_iso_square
    (hk : Function.Surjective (algebraMap k K))
    (hL : Module.finrank L M = 1)
    (x : rationalPoints ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp) :
    rationalNorm K M ((CommGroupScheme.baseChange (baseMap k K)).obj T)
        (squareRationalExtend k K L M T x) =
      rationalExtend k K T.toGrp (rationalNorm k L T x) :=
  norm_square_of_injective
    (rationalNorm k K T) (rationalNorm k L T) (rationalNorm k M T)
    (rationalNorm K M ((CommGroupScheme.baseChange (baseMap k K)).obj T))
    (rationalNorm L M ((CommGroupScheme.baseChange (baseMap k L)).obj T))
    (rationalExtend k K T.toGrp)
    (rationalExtend L M ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp)
    (commTowerRationalEquiv k K M T).toEquiv
    (commTowerRationalEquiv k L M T).toEquiv
    (rationalNorm_injective_of_surjective k K T hk)
    (rationalNorm_commTowerRationalEquiv k K M T)
    (rationalNorm_commTowerRationalEquiv k L M T)
    (rationalNorm_extend_of_finrank_one k K T
      (Module.finrank_of_bijective_algebraMap ⟨(algebraMap k K).injective, hk⟩))
    (rationalNorm_extend_of_finrank_one L M
      ((CommGroupScheme.baseChange (baseMap k L)).obj T) hL) x

variable {ΓL ΓM : Type*} [LinearOrderedCommGroupWithZero ΓL]
  [LinearOrderedCommGroupWithZero ΓM]
  (vL : Valuation L ΓL) (vM : Valuation M ΓM) [vL.HasExtension vM]

omit [FiniteDimensional k K] [FiniteDimensional k L]
  [FiniteDimensional k M] [FiniteDimensional K M]
  [IsGalois k K] [IsGalois k L] [IsGalois k M] [IsGalois K M] in
private theorem squareRationalExtend_mem_kernel
    (hinv : ∀ (σ : M ≃ₐ[L] M) (z : M), vM (σ z) = vM z)
    (x : rationalPoints ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp)
    (hx : x ∈ characterValuationKernel vL
      ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp) :
    squareRationalExtend k K L M T x ∈ characterValuationKernel vM
      ((CommGroupScheme.baseChange (baseMap K M)).obj
        ((CommGroupScheme.baseChange (baseMap k K)).obj T)).toGrp := by
  apply mulEquiv_symm_mem_characterValuationKernel vM
    (towerBaseChangeIso k K M T.toGrp) (commTowerRationalEquiv k K M T)
    (commTowerRationalEquiv_apply k K M T)
  exact map_characterValuationKernel_le vM (towerBaseChangeIso k L M T.toGrp).hom
    ⟨rationalExtend L M ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp x,
      characterValuationKernel_le_comap vL vM hinv
        ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp hx,
      (commTowerRationalEquiv_apply k L M T _).symm⟩

/-- Coefficient extension preserves the bounded norm image in a field square
with degree-one horizontal sides. -/
theorem map_torusNormIwahori_le_iso_square
    (hk : Function.Surjective (algebraMap k K))
    (hL : Module.finrank L M = 1)
    (hinv : ∀ (σ : M ≃ₐ[L] M) (z : M), vM (σ z) = vM z) :
    (torusNormIwahori k L vL T).map (rationalExtend k K T.toGrp) ≤
      torusNormIwahori K M vM ((CommGroupScheme.baseChange (baseMap k K)).obj T) := by
  exact subgroup_map_le_of_square _ _
    (rationalNorm k L T) (rationalExtend k K T.toGrp)
    (squareRationalExtend k K L M T)
    (rationalNorm K M ((CommGroupScheme.baseChange (baseMap k K)).obj T))
    (rationalNorm_iso_square k K L M T hk hL)
    (squareRationalExtend_mem_kernel k K L M T vL vM hinv)

end Square


end Langlands.Geometry.Building
