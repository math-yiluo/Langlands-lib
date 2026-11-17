import Langlands.GroupScheme.Reductive.RelativeIsogenyRootRestriction
import Langlands.GroupScheme.Reductive.DynamicCutRootParametrization

/-! # Actual supplied-root restrictions over arbitrary rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- A single residue field of a nonzero ring identifies the full coordinate pairing. -/
theorem IsFibrewiseRootDatumOf.pairing_of_nontrivial [Nontrivial R]
    (hP : IsFibrewiseRootDatumOf I G i P) (m n : I → ℤ) :
    P.toLinearMap m n = ∑ a, m a * n a := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal R
  let : M.IsMaximal := hM
  let : Field (R ⧸ M) := Ideal.Quotient.field M
  exact hP.pairing (R ⧸ M) m n

end Langlands.GroupScheme

namespace Langlands.GroupScheme.SuppliedRootIsogeny

open LocalRootGroup LocalSplitCell

variable {R : Type u} [CommRing R]
  {I I' : Type u} [Fintype I] [Fintype I']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
  {J J' : Type u} [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced]
  (hP : IsFibrewiseRootDatumOf I G i P) (hQ : IsFibrewiseRootDatumOf I' H j Q)
  {p : ℕ} (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)

include hP hQ

/-- The transpose identity is the actual coordinate dot-product identity. -/
theorem dot_coweightMap [Nontrivial R] (x : I' → ℤ) (y : I → ℤ) :
    ∑ a, x a * r.coweightMap y a = ∑ a, r.weightMap x a * y a := by
  rw [← hQ.pairing_of_nontrivial,
    ← hP.pairing_of_nontrivial]
  exact (r.pairing_apply x y).symm

/-- A root pairs with the transported cocharacter by its positive root factor. -/
theorem root_dot_coweightMap [Nontrivial R] (b : J') (y : I → ℤ) :
    ∑ a, Q.root b a * r.coweightMap y a =
      (r.rootFactor b : ℤ) * ∑ a, P.root (r.indexEquiv b) a * y a := by
  rw [dot_coweightMap i j hP hQ r, r.root_weightMap]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- Isolation of a source root pair is preserved by the contravariant
cocharacter map of a supplied root-datum isogeny. -/
theorem isolating_coweightMap [Nontrivial R] (b : J') (mu : I → ℤ)
    (hmu : ∀ a : J, ∑ k, P.root a k * mu k = 0 →
      P.root a = P.root (r.indexEquiv b) ∨ P.root a = -P.root (r.indexEquiv b)) :
    ∀ c : J', ∑ k, Q.root c k * r.coweightMap mu k = 0 →
      Q.root c = Q.root b ∨ Q.root c = -Q.root b := by
  intro c hc
  rw [root_dot_coweightMap i j hP hQ r] at hc
  have hq : (r.rootFactor c : ℤ) ≠ 0 := by
    exact_mod_cast (r.rootFactor_pos c).ne'
  exact r.root_eq_or_neg_of_corresponding_roots (hmu _ ((mul_eq_zero.mp hc).resolve_left hq))

variable (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
    splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
  (hweight : ∀ m : I' → ℤ, tau ≫ splitTorus.exponentCharacter _ I' m =
    splitTorus.exponentCharacter _ I (r.weightMap m))

include hweight

/-- Compatibility on actual exponent characters forces compatibility on
actual cocharacters over the whole, possibly nonreduced, base. -/
theorem cocharacter_comp_torusHom [Nontrivial R] (mu : I → ℤ) :
    splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I mu ≫ tau =
      splitTorus.exponentCocharacter _ I' (r.coweightMap mu) := by
  classical
  apply splitTorus.hom_ext_projections _ I'
  intro a
  have hproj : splitTorus.proj (Spec (CommRingCat.of R)) I' a =
      splitTorus.exponentCharacter _ I' (Pi.single a 1) := by
    simp [splitTorus.exponentCharacter, Pi.single_apply]
  rw [Category.assoc, hproj, hweight,
    splitTorus.exponentCocharacter_comp_exponentCharacter,
    splitTorus.exponentCocharacter_comp_exponentCharacter,
    ← dot_coweightMap i j hP hQ r]

variable (phi : G ⟶ H)
  (hphi : i ≫ phi = CommGroupScheme.groupHom tau ≫ j)

include hphi

/-- The actual ambient cocharacter squares induced by the torus square. -/
theorem ambient_cocharacter_square [Nontrivial R] (mu : I → ℤ) :
    (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I mu) ≫ i) ≫ phi =
      CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter _ I' (r.coweightMap mu)) ≫ j := by
  rw [Category.assoc, hphi, ← Category.assoc]
  change CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I mu ≫ tau) ≫ j = _
  rw [cocharacter_comp_torusHom i j hP hQ r tau hweight]

/-- An actual compatible homomorphism carries each source root subgroup into
the root selected by the supplied root-datum isogeny, on every test scheme. -/
theorem subgroup_le_comap (hH : IsReductive H)
    (hmaxH : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
    (b : J') {v : Ga R ⟶ H}
    (hv : IsRootParametrization j (Q.root b) v) :
    RelativeRoot.subgroup (S := splitTorus.commGroupScheme _ I) i
        (splitTorus.exponentCharacter _ I (P.root (r.indexEquiv b))) ≤
      (RelativeRoot.subgroup (S := splitTorus.commGroupScheme _ I') j
        (splitTorus.exponentCharacter _ I' (Q.root b))).comap phi := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · let := hR
    let : IsEmpty (Spec (CommRingCat.of R)) :=
      (PrimeSpectrum.isEmpty_iff_subsingleton (R := R)).mpr inferInstance
    intro T x _
    let : IsEmpty T.left := T.hom.base.hom.1.isEmpty
    have hx : x ≫ phi.hom.hom = 1 := by
      apply Over.OverMorphism.ext
      exact isInitialOfIsEmpty.hom_ext _ _
    rw [SubgroupFunctor.mem_comap, hx]
    exact one_mem _
  · let := hR
    have := hH.smooth
    obtain ⟨mu, hmu0, hmu⟩ := exists_kernel_exponent P (ULift.{u} ℚ) (r.indexEquiv b)
    let nu := P.coroot (r.indexEquiv b)
    have htwo : ∑ k, P.root (r.indexEquiv b) k * nu k = ((2 : ℕ) : ℤ) := by
      rw [← hP.pairing_of_nontrivial, P.root_coroot_two]
      rfl
    have ht0 : ∑ k, Q.root b k * r.coweightMap mu k = 0 := by
      rw [root_dot_coweightMap i j hP hQ r, hmu0, mul_zero]
    have htnu : ∑ k, Q.root b k * r.coweightMap nu k =
        ((r.rootFactor b * 2 : ℕ) : ℤ) := by
      rw [root_dot_coweightMap i j hP hQ r, htwo, Nat.cast_mul, Nat.cast_ofNat]
    have hd : 0 < r.rootFactor b * 2 := Nat.mul_pos (r.rootFactor_pos b) two_pos
    have hfib := hasEquivariantFibres_of_isolating_cocharacters j Q hH hmaxH hQ b
      (r.coweightMap mu) (r.coweightMap nu) ht0
      (isolating_coweightMap i j hP hQ r b mu hmu) (by rw [htnu]; exact_mod_cast hd)
    have hcut := subgroup_eq_dynamicCut_of_parametrization j (r.coweightMap mu) (r.coweightMap nu)
      (Q.root b) ht0 hd htnu hv hfib
    intro T x hx
    change x ≫ phi.hom.hom ∈
      (RelativeRoot.subgroup (S := splitTorus.commGroupScheme _ I') j
        (splitTorus.exponentCharacter _ I' (Q.root b))).carrier T
    rw [hcut]
    have hC := Dynamic.centralizer_le_comap
      (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I mu) ≫ i) phi T
      (subgroup_le_centralizer i mu (P.root (r.indexEquiv b)) hmu0 T hx)
    have hU := Dynamic.unipotent_le_comap
      (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I nu) ≫ i) phi T
      (subgroup_le_unipotent i nu (P.root (r.indexEquiv b)) two_pos htwo T hx)
    rw [SubgroupFunctor.mem_comap,
      ambient_cocharacter_square i j hP hQ r tau hweight phi hphi] at hC hU
    exact ⟨hC, hU⟩

variable (hH : IsReductive H)
  (hmaxH : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  (b : J')

/-- Restrict a compatible homomorphism to any supplied source and target
actual root parametrizations. -/
def rootRestriction {u : Ga R ⟶ G} {v : Ga R ⟶ H}
    (hu : IsRootParametrization i (P.root (r.indexEquiv b)) u)
    (hv : IsRootParametrization j (Q.root b) v) : Ga R ⟶ Ga R :=
  hu.represents.restrictionHom hv.represents phi
    (subgroup_le_comap i j hP hQ r tau hweight phi hphi hH hmaxH b hv)

/-- The actual restriction commutes with the given ambient homomorphism. -/
theorem rootRestriction_comp {u : Ga R ⟶ G} {v : Ga R ⟶ H}
    (hu : IsRootParametrization i (P.root (r.indexEquiv b)) u)
    (hv : IsRootParametrization j (Q.root b) v) :
    rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv ≫ v = u ≫ phi :=
  hu.represents.restrictionHom_comp hv.represents phi
    (subgroup_le_comap i j hP hQ r tau hweight phi hphi hH hmaxH b hv)

end Langlands.GroupScheme.SuppliedRootIsogeny
