import Langlands.GroupScheme.Examples.QuasiSplitUnitaryRelativeRootsStatement
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryRankProof
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryReductiveProof
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamicProof
import Langlands.GroupScheme.Examples.QuasiSplitUnitarySplittingCocharacter
import Langlands.GroupScheme.Rational.GenericMinimalParabolicProof
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Rational.CrossTorusLieTransport
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Torus.RootSupportBaseChange
import Langlands.GroupScheme.Torus.WeightRestriction
import Langlands.GroupScheme.Torus.SplitMono
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Reductive.GeneralLinearRoots
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # Relative roots and the minimal parabolic of the quasi-split unitary group `U(1,1)`:
proof -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

/-! ### Roots of the diagonal cocharacter `t ↦ diag(t, t⁻¹)` of `GL₂` -/

section GeneralLinear

variable (E : Type u) [Field E]

/-- The cocharacter `t ↦ (t, t⁻¹)` of the diagonal torus of `GL₂`. -/
abbrev hyperbolicCocharacter :
    cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of E)) (ULift.{u} (Fin 2))) :=
  (splitTorus.cocharacterLatticeEquiv E (ULift.{u} (Fin 2))).symm fun i => weights 1 i.down

/-- The pairing of `eₐ - e_b` with `(1, -1)`. -/
theorem pairing_root_hyperbolic (a b : Fin 2) (hab : a ≠ b) :
    gmEndEquiv E (hyperbolicCocharacter E ≫
        (splitTorus.characterLatticeEquiv E (ULift.{u} (Fin 2))).symm
          (Pi.single (ULift.up a) 1 - Pi.single (ULift.up b) 1)) =
      weights 1 a - weights 1 b := by
  rw [← latticePairing_apply, splitTorus.latticePairing_symm_symm]
  rw [← Equiv.ulift.symm.sum_comp]
  fin_cases a <;> fin_cases b <;> first
    | exact absurd rfl hab
    | simp [Fin.sum_univ_two, weights, Pi.single_apply]

/-- The roots of `t ↦ diag(t, t⁻¹)` in `GL₂` are the characters `t ↦ t²` and `t ↦ t⁻²`. -/
theorem mem_roots_diagonalCocharacter_iff
    (ψ : characterLattice (Gm (Spec (CommRingCat.of E)))) :
    ψ ∈ roots (GeneralLinear.diagonalCocharacter (Fin 2) (CommRingCat.of E) (weights 1)) ↔
      gmEndEquiv E ψ = 2 ∨ gmEndEquiv E ψ = -2 := by
  have : Smooth (GeneralLinear.groupScheme (Fin 2) (CommRingCat.of E)).X.hom :=
    GeneralLinear.smoothStatement _ _
  rw [← GeneralLinear.cocharacterLatticeEquiv_symm_comp_diagonalTorus E (weights 1),
    mem_roots_comp_iff (isSplitTorus_splitTorus _) isSplitTorus_gm,
    GeneralLinear.roots_diagonalTorus]
  constructor
  · rintro ⟨-, χ, ⟨a, b, hab, hχ⟩, rfl⟩
    have hχ' : χ = (splitTorus.characterLatticeEquiv E (ULift.{u} (Fin 2))).symm
        (Pi.single (ULift.up a) 1 - Pi.single (ULift.up b) 1) := by
      rw [← hχ, AddEquiv.symm_apply_apply]
    rw [hχ', pairing_root_hyperbolic E a b hab]
    fin_cases a <;> fin_cases b <;> first
      | exact absurd rfl hab
      | simp [weights]
  · intro hψ
    have hψ0 : ψ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hψ
      omega
    refine ⟨hψ0, ?_⟩
    rcases hψ with h | h
    · refine ⟨_, ⟨0, 1, by decide, AddEquiv.apply_symm_apply _ _⟩, ?_⟩
      apply (gmEndEquiv E).injective
      rw [pairing_root_hyperbolic E 0 1 (by decide), h]
      simp [weights]
    · refine ⟨_, ⟨1, 0, by decide, AddEquiv.apply_symm_apply _ _⟩, ?_⟩
      apply (gmEndEquiv E).injective
      rw [pairing_root_hyperbolic E 1 0 (by decide), h]
      simp [weights]

end GeneralLinear

variable {F E : Type u} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  {κ : Type u} [Fintype κ] (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E)

/-! ### Maximality -/

/-- The image of `λ` is a maximal split torus: a split torus containing it has rank at most one
by the rank bound, so the factorization `𝔾ₘ ⟶ T'` is a monomorphism between split tori of
rank one. -/
theorem isMaximalSplitTorus_cocharacter (hc : c ≠ AlgEquiv.refl) :
    IsMaximalSplitTorus (cocharacter b c) := by
  obtain ⟨hcl, hrank, -⟩ := rankStatement F E κ b c hc
  refine ⟨⟨isSplitTorus_gm, hcl⟩, ?_⟩
  intro T' i' hi' f hf
  obtain ⟨J, hJ, ⟨eK⟩⟩ := hi'.1
  have hJ1 : Nat.card J ≤ 1 :=
    hrank J (eK.inv ≫ i') ((IsClosedSubgroup.of_iso eK.symm).comp hi'.2)
  have hmono : Mono f.hom.hom := by
    have : Mono (cocharacter b c).hom.hom := hcl.mono_overHom
    have hfac : f.hom.hom ≫ i'.hom.hom = (cocharacter b c).hom.hom := by
      rw [← hf]
      rfl
    exact mono_of_mono_fac hfac
  exact splitTorus.isIso_of_mono_of_iso (splitTorus.gmIso _) eK f hmono
    (by simpa using hJ1)

/-! ### Relative roots -/

section Roots

local notation "β" => algebraBaseMap F E

local instance baseChangeAffine (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] : IsAffineHom ((GroupScheme.baseChange β).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom β)
  infer_instance

omit [Algebra.IsQuadraticExtension F E] in
/-- Base change to `E` followed by the identification of the base change of `𝔾ₘ` keeps the
exponent of a character of `𝔾ₘ`. -/
theorem gmEndEquiv_congr_baseChange (χ : characterLattice (Gm (Spec (CommRingCat.of F)))) :
    gmEndEquiv E (characterLattice.congr (Gm.commBaseChangeIso β)
        (characterLattice.baseChange β _ χ)) = gmEndEquiv F χ :=
  gmEndEquiv_baseChange β χ

/-- The relative roots of `λ`, in terms of exponents. -/
theorem mem_relativeRoots_cocharacter_iff (hc : c ≠ AlgEquiv.refl)
    (χ : characterLattice (Gm (Spec (CommRingCat.of F)))) :
    χ ∈ relativeRoots (cocharacter b c) ↔ gmEndEquiv F χ = 2 ∨ gmEndEquiv F χ = -2 := by
  have hG := isConnectedReductive F E κ b c hc
  have : Smooth (groupScheme b c).X.hom := hG.smooth
  have htr : (GroupScheme.baseChange β).map (cocharacter b c) ≫ (splittingIso b c hc).hom =
      CommGroupScheme.groupHom (Gm.commBaseChangeIso β).hom ≫
        GeneralLinear.diagonalCocharacter (Fin 2) (CommRingCat.of E) (weights 1) := by
    rw [← baseChangeCocharacter_cocharacter_splittingIso b c hc, baseChangeCocharacter,
      Gm.groupHom_commBaseChangeIso_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [relativeRoots_eq_roots,
    ← mem_roots_baseChange_iff (K := E) (groupScheme b c) (Gm (Spec (CommRingCat.of F)))
      isSplitTorus_gm (cocharacter b c) χ,
    ← roots_mem_of_transport_iff (Gm.commBaseChangeIso β) (splittingIso b c hc) htr,
    mem_roots_diagonalCocharacter_iff, gmEndEquiv_congr_baseChange]

/-- The relative roots of `λ` are the characters `t ↦ t²` and `t ↦ t⁻²`. -/
theorem relativeRoots_cocharacter (hc : c ≠ AlgEquiv.refl) :
    relativeRoots (cocharacter b c) =
      {Gm.powerHom (Spec (CommRingCat.of F)) 2, Gm.powerHom (Spec (CommRingCat.of F)) (-2)} := by
  ext χ
  rw [mem_relativeRoots_cocharacter_iff b c hc, Set.mem_insert_iff, Set.mem_singleton_iff,
    Gm.powerHom_apply, Gm.powerHom_apply]
  constructor
  · rintro (h | h)
    · left
      rw [eq_gmEndEquiv_zsmul F χ, h]
    · right
      rw [eq_gmEndEquiv_zsmul F χ, h]
  · rintro (rfl | rfl)
    · left
      exact gmEndEquiv_zsmul_id F 2
    · right
      exact gmEndEquiv_zsmul_id F (-2)

end Roots

/-! ### Generic cocharacters -/

/-- A cocharacter `n` of `𝔾ₘ` composed with `λ` is the cocharacter with weights `(n, -n)`. -/
theorem zsmul_comp_cocharacter (n : ℤ) :
    CommGroupScheme.groupHom (n • 𝟙 (Gm (Spec (CommRingCat.of F)))) ≫ cocharacter b c =
      weightCocharacter b c n := by
  apply hom_ext_points
  intro T x
  apply (pointsEquiv b c T).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, Gm.comp_zsmul_id, pointsEquiv_weightCocharacter,
    pointsEquiv_weightCocharacter, map_zpow]
  apply Subtype.ext
  apply Units.ext
  rw [diagonalUnitary_val, diagonalUnitary_val]
  congr 1
  funext i
  fin_cases i <;> simp [weights]

/-- For `n ≠ 0`, the cocharacter with weights `(n, -n)` has the diagonal subgroup as dynamic
Levi subgroup. -/
theorem centralizer_weightCocharacter {n : ℤ} (hn : n ≠ 0) :
    Dynamic.centralizer (weightCocharacter b c n) = diagonal b c := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  rw [mem_centralizer_weightCocharacter_iff]
  change (∀ i j, weights n i ≠ weights n j → matrixCoordinates b c T g i j = 0) ↔
    (∀ i j, weights 1 i ≠ weights 1 j → matrixCoordinates b c T g i j = 0)
  have h : ∀ i j : Fin 2, weights n i ≠ weights n j ↔ weights 1 i ≠ weights 1 j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [weights] <;> omega
  simp only [h]

/-- The relative roots and the minimal parabolic of `U(1,1)`: maximality, the roots `±2`,
genericity of the identity cocharacter, and minimality and the dynamic Levi subgroup for every
generic cocharacter. -/
theorem relativeRootsStatement : RelativeRootsStatement.{u} := by
  intro F E _ _ _ _ κ _ b c hc
  have h1 := isMaximalSplitTorus_cocharacter b c hc
  have h2 := relativeRoots_cocharacter b c hc
  have hpair : ∀ ν : cocharacterLattice (Gm (Spec (CommRingCat.of F))),
      IsGenericCocharacter (cocharacter b c) ν ↔ gmEndEquiv F ν ≠ 0 := by
    intro ν
    rw [isGenericCocharacter_iff, h2]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
      latticePairing_apply, Gm.powerHom_apply]
    rw [gmEndEquiv_comp, gmEndEquiv_comp, gmEndEquiv_zsmul_id, gmEndEquiv_zsmul_id]
    constructor
    · rintro ⟨h, -⟩
      intro h0
      apply h
      rw [h0, zero_mul]
    · intro h
      exact ⟨mul_ne_zero h (by norm_num), mul_ne_zero h (by norm_num)⟩
  refine ⟨h1, h2, (hpair _).mpr (by simp), fun ν hν => ⟨?_, ?_⟩⟩
  · exact genericMinimalParabolic F (groupScheme b c) (isConnectedReductive F E κ b c hc)
      (Gm (Spec (CommRingCat.of F))) (cocharacter b c) h1 ν hν
  · have hn : gmEndEquiv F ν ≠ 0 := (hpair ν).mp hν
    rw [eq_gmEndEquiv_zsmul F ν, zsmul_comp_cocharacter, torusCentralizer_gm_eq_dynamicCentralizer,
      centralizer_cocharacter, centralizer_weightCocharacter b c hn]

end Langlands.GroupScheme.QuasiSplitUnitary
