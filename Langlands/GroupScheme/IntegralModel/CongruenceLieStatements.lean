import Langlands.GroupScheme.IntegralModel.CongruenceLie
import Langlands.GroupScheme.IntegralModel.LieLatticeAdjoint
import Langlands.GroupScheme.IntegralModel.CongruenceLifting
import Langlands.GroupScheme.Dilatation.CongruenceModel

/-! # Kernel, lifting, and naturality of the congruence–Lie homomorphism -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

section LatticeQuotients

variable {R K A B : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  [CommRing A] [IsDomain A] [Field B] [Algebra A B] [IsFractionRing A B] [IsLocalRing A]
  {G : GroupScheme (Spec (CommRingCat.of K))} {H : GroupScheme (Spec (CommRingCat.of B))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (M : IntegralModel R K G) (N : IntegralModel A B H)
  {σ : R →+* A} (d : GenericLie R G →ₛₗ[σ] GenericLie A H)
  (hL : M.lieLattice ≤ N.lieLattice.comap d)
  (h𝔪 : (IsLocalRing.maximalIdeal R).map σ ≤ IsLocalRing.maximalIdeal A)

include hL h𝔪 in
private theorem lieLatticeAt_le_comap (n : ℕ+) :
    M.lieLatticeAt n ≤ (N.lieLatticeAt n).comap d := by
  have hpow : ((IsLocalRing.maximalIdeal R) ^ (n : ℕ)).map σ ≤
      (IsLocalRing.maximalIdeal A) ^ (n : ℕ) := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' h𝔪 _
  refine Submodule.smul_le.mpr (fun a ha X hX => ?_)
  change d (a • X) ∈ N.lieLatticeAt n
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem_smul (hpow (Ideal.mem_map_of_mem σ ha)) (hL hX)

/-- A semilinear map respecting the lattices and carrying the original maximal
ideal into the target maximal ideal induces the map of their power quotients. -/
def lieLatticeQuotientMap (n m : ℕ+) :
    M.congruenceLieQuotient n m →ₛₗ[σ] N.congruenceLieQuotient n m :=
  ((M.lieLatticeAt m).comap (M.lieLatticeAt n).subtype).mapQ
    ((N.lieLatticeAt m).comap (N.lieLatticeAt n).subtype)
    (LinearMap.codRestrict _ (d.comp (M.lieLatticeAt n).subtype)
      (fun x => M.lieLatticeAt_le_comap N d hL h𝔪 n x.property))
    (fun _ hx => M.lieLatticeAt_le_comap N d hL h𝔪 m hx)

end LatticeQuotients

section Maps

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsLocalRing R]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  {M : IntegralModel R K G} {N : IntegralModel R K H} {f : G ⟶ H}

/-- The restriction of a model homomorphism's generic map to its congruence subgroups. -/
def Hom.congruenceSubgroupMap (φ : M.Hom N f) (n : ℕ+) :
    M.congruenceSubgroupAt n →* N.congruenceSubgroupAt n :=
  ((rationalPoints.map f).comp (M.congruenceSubgroupAt n).subtype).codRestrict _
    (fun g => φ.map_mem_congruenceSubgroupAt n g.property)

/-- Conjugation by an integral point on the level-`n` congruence subgroup. -/
def congruenceSubgroupConj (M : IntegralModel R K G) (h : M.integralPoints) (n : ℕ+) :
    M.congruenceSubgroupAt n →* M.congruenceSubgroupAt n :=
  ((MulAut.conj h.val).toMonoidHom.comp (M.congruenceSubgroupAt n).subtype).codRestrict _
    (fun g => by
      let y := Subgroup.inclusion (M.congruenceSubgroupAt_le_integralPoints n) g
      have hn : ((M.congruenceSubgroupAt n).subgroupOf M.integralPoints).Normal := inferInstance
      exact hn.conj_mem y g.property h)

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- The differential of a model homomorphism on the actual Lie-lattice quotients. -/
def Hom.congruenceLieQuotientMap (φ : M.Hom N f) (n m : ℕ+) :
    M.congruenceLieQuotient n m →ₗ[R] N.congruenceLieQuotient n m :=
  M.lieLatticeQuotientMap N (GenericLie.map R f)
    (Submodule.map_le_iff_le_comap.mp φ.map_lieLattice_le) (by simp) n m

/-- The adjoint action of an integral point on the actual Lie-lattice quotient. -/
def congruenceLieQuotientAdjoint (M : IntegralModel R K G) (h : M.integralPoints)
    (n m : ℕ+) : M.congruenceLieQuotient n m →ₗ[R] M.congruenceLieQuotient n m :=
  M.lieLatticeQuotientMap M (GenericLie.adjoint R h.val)
    (fun _ hX => M.adjoint_mem_lieLattice h.property hX) (by simp) n m

end Maps

/-- KP A.5.19(3), kernel and injectivity over the original coefficient ring. -/
def CongruenceLieInjectivityStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    (M : IntegralModel R K G) (hM : M.IsSmooth) (n m : ℕ+) (h : n ≤ m)
    (hm : (m : ℕ) ≤ 2 * (n : ℕ)),
    (M.congruenceLieHom hM h hm).ker =
      (M.congruenceSubgroupAt m).subgroupOf (M.congruenceSubgroupAt n) ∧
    Function.Injective (M.congruenceLieQuotientHom hM h hm)

/-- KP A.5.19(3), surjectivity and quotient bijectivity over a Henselian local base. -/
def CongruenceLieSurjectivityStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    (M : IntegralModel R K G) (hM : M.IsSmooth) (n m : ℕ+) (h : n ≤ m)
    (hm : (m : ℕ) ≤ 2 * (n : ℕ)),
    Function.Surjective (M.congruenceLieHom hM h hm) ∧
    Function.Bijective (M.congruenceLieQuotientHom hM h hm)

/-- KP A.5.19(3), functoriality of the constructed congruence–Lie map in the model. -/
def CongruenceLieFunctorialityStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (M : IntegralModel R K G) (N : IntegralModel R K H) (hM : M.IsSmooth) (hN : N.IsSmooth)
    (f : G ⟶ H) (φ : M.Hom N f) (n m : ℕ+) (h : n ≤ m) (hm : (m : ℕ) ≤ 2 * (n : ℕ)),
    (N.congruenceLieHom hN h hm).comp (φ.congruenceSubgroupMap n) =
      ((φ.congruenceLieQuotientMap n m).toAddMonoidHom.toMultiplicative).comp
        (M.congruenceLieHom hM h hm)

/-- The congruence–Lie map intertwines integral conjugation and the differential
adjoint action on the Lie-lattice quotient. -/
def CongruenceLieAdjointEquivarianceStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    (M : IntegralModel R K G) (hM : M.IsSmooth) (g : M.integralPoints)
    (n m : ℕ+) (h : n ≤ m) (hm : (m : ℕ) ≤ 2 * (n : ℕ)),
    (M.congruenceLieHom hM h hm).comp (M.congruenceSubgroupConj g n) =
      ((M.congruenceLieQuotientAdjoint g n m).toAddMonoidHom.toMultiplicative).comp
        (M.congruenceLieHom hM h hm)

/-- KP A.5.13(4), Lie lattices of the actual congruence group schemes, including level zero. -/
def CongruenceModelLieLatticeStatement : Prop :=
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    (M : IntegralModel R K G) (ϖ : R) (hϖ : Irreducible ϖ) (n : ℕ),
    (M.congruenceModel hϖ n).lieLattice = (IsLocalRing.maximalIdeal R) ^ n • M.lieLattice

/-- The kernel, Henselian surjectivity, and model functoriality of the canonical
congruence–Lie map, together with its adjoint equivariance and the congruence-model lattice formula. -/
def CongruenceLiePropertiesStatement : Prop :=
  CongruenceLieInjectivityStatement.{u} ∧ CongruenceLieSurjectivityStatement.{u} ∧
  CongruenceLieFunctorialityStatement.{u} ∧ CongruenceLieAdjointEquivarianceStatement.{u} ∧
  CongruenceModelLieLatticeStatement.{u}

end Langlands.GroupScheme.IntegralModel
