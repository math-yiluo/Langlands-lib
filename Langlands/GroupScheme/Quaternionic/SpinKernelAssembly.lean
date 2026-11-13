import Langlands.GroupScheme.Quaternionic.LeviGroupScheme
import Langlands.GroupScheme.Quaternionic.LocalSpinKneserTitsReduction

/-!
# The quaternionic Kneser–Tits statement from the spin-kernel statements

For a spin cover `π : S ⟶ O(q)` and a hyperbolic pair `h` of `q`, a pair `(μ, ψ)` of lifts of
the Levi morphism `leviHom h` on the scalars and on `SL₁(D)` (`IsLeviLift`) defines
`z(u) = μ(u) ψ(u · 1)` on `μ₂`. Three statements are formulated in the setting of
`LocalSpinKneserTitsStatement`:

* `SpinLeviLiftStatement`: such lifts exist;
* `SpinKernelGeneratorStatement`: for all such lifts, `z` is a bijection from `μ₂` onto
  `ker π` on all coefficient algebras (`KernelGenerator`);
* `SpinKernelElementaryLiftStatement`: for all such lifts, the rational point `z(-1)` lies in
  `S(K)⁺`.

`localSpinKneserTits_of_spinKernel` derives `LocalSpinKneserTitsStatement` from the three.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite Langlands.CentralSimple
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Quaternionic.SpinKernel

open LeviScheme FirstKindInvolution.Eichler

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] {σ : FirstKindInvolution K D} {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}

/-- `(μ, ψ)` lift the Levi morphism `leviHom h` on the scalars and on `SL₁(D)`. -/
def IsLeviLift {e f : n → D} (h : σ.IsHyperbolicPair q e f) (π : S ⟶ σ.isometryGroup q)
    (mu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S) (psi : CentralSimpleUnits.normOne K D ⟶ S) :
    Prop :=
  (∀ (A : CommAlgCat.{u} (CommRingCat.of K)) (t : Aˣ),
      (gmPoint A t ≫ mu.hom.hom) ≫ π.hom.hom =
        unitMap (leviHom h) A (normCoverScalarUnits K D A t)) ∧
    psi ≫ π = CentralSimpleUnits.normOneι K D ≫ leviHom h

omit [Algebra.IsCentral K D] in
/-- The kernel of a spin cover is central on points over every coefficient algebra. -/
theorem commute_of_comp_eq_one (hπ : σ.IsSpinCover q π) (A : CommAlgCat.{u} (CommRingCat.of K))
    (x y : S.affinePoints A) (hx : x ≫ π.hom.hom = 1) : Commute x y := by
  have := hπ.smooth
  obtain ⟨p, hp, hpπ⟩ := hπ.exists_centralIsogeny
  have : Mono (identityComponentι (σ.isometryGroup q)).hom.hom :=
    (IdentityComponent.isClosedSubgroup_identityComponentι (σ.isometryGroup q)).mono_overHom
  have hx' : x ≫ p.hom.hom = 1 := by
    apply (cancel_mono (identityComponentι (σ.isometryGroup q)).hom.hom).mp
    rw [Category.assoc, ← Grp.comp_hom_hom, hpπ, hx, MonObj.one_comp]
  exact commute_of_mem_center (((isCentral_kernelι_iff p).mp hp.isCentral_kernelι) _ x hx') y

/-- **Spin input 1 for one cover.** -/
theorem leviReducedNormSquare_of_kernelGenerator (hdeg : reducedDegree K D = 2)
    (hπ : σ.IsSpinCover q π) {e f : n → D} (h : σ.IsHyperbolicPair q e f)
    {mu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S} {psi : CentralSimpleUnits.normOne K D ⟶ S}
    (hl : IsLeviLift h π mu psi) (hZ : KernelGenerator hdeg π mu psi)
    (s : rationalPoints S) (a : Dˣ)
    (hs : isometryRationalMatrix σ q (rationalPoints.map π s) =
      levi σ q (isHyperbolic_of_isHyperbolicPair h) a) :
    ∃ t : K, reducedNorm K D K (1 ⊗ₜ[K] (a : D)) = t ^ 2 := by
  refine exists_sq_eq_reducedNorm_of_comp_eq (Λ := leviHom h) (commute_of_comp_eq_one hπ)
    hl.1 hl.2 hZ s a ?_
  apply isometryRationalMatrix_injective σ q
  rw [hs, isometryRationalMatrix_leviHom]

/-- The element `-1` of `μ₂(K)`. -/
def negOneRoot : rootsOfUnity 2 (CommAlgCat.of (CommRingCat.of K) K) :=
  ⟨-1, by rw [mem_rootsOfUnity, neg_one_sq]⟩

theorem kernelPoint_one (hdeg : reducedDegree K D = 2)
    (mu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S) (psi : CentralSimpleUnits.normOne K D ⟶ S)
    (A : CommAlgCat.{u} (CommRingCat.of K)) :
    kernelPoint hdeg mu psi A 1 = 1 := by
  simp only [kernelPoint, map_one, OneMemClass.coe_one, MonObj.one_comp, mul_one]

/-- **Spin input 2 for one cover.** -/
theorem kernelElementary_of_kernelGenerator (hdeg : reducedDegree K D = 2)
    {mu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S} {psi : CentralSimpleUnits.normOne K D ⟶ S}
    (hZ : KernelGenerator hdeg π mu psi)
    (hneg : (GaloisPointComparison.rationalCoeffEquiv K S).symm
      (kernelPoint hdeg mu psi _ negOneRoot) ∈ parabolicElementarySubgroup S)
    (s : rationalPoints S) (hs : rationalPoints.map π s = 1) :
    s ∈ parabolicElementarySubgroup S := by
  have hk : GaloisPointComparison.rationalCoeffEquiv K S s ≫ π.hom.hom = 1 := by
    rw [rationalCoeffEquiv_comp_hom, hs, map_one]
  obtain ⟨w, hw, -⟩ := hZ _ _ hk
  have hw2 : (w : Kˣ) = 1 ∨ (w : Kˣ) = -1 := by
    have h2 : ((w : Kˣ) : K) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity 2 _).mp w.2, Units.val_one]
    rcases sq_eq_one_iff.mp h2 with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)
  have hs' : s = (GaloisPointComparison.rationalCoeffEquiv K S).symm
      (kernelPoint hdeg mu psi _ w) := by
    rw [hw, MulEquiv.symm_apply_apply]
  rcases hw2 with h1 | h1
  · have : w = 1 := Subtype.ext h1
    rw [hs', this, kernelPoint_one, map_one]
    exact Subgroup.one_mem _
  · have : w = negOneRoot := Subtype.ext h1
    rw [hs', this]
    exact hneg

/-! ### Statements in the setting of `LocalSpinKneserTitsStatement` -/

/-- **Lifts exist.** In the setting of `LocalSpinKneserTitsStatement`, for every spin cover
`π` and every hyperbolic pair `h`, there are lifts `(μ, ψ)` of the Levi morphism. -/
def SpinLeviLiftStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D],
    Module.finrank K D = 4 →
    ∀ σ : FirstKindInvolution K D, Module.finrank K σ.symmetricSubspace = 3 →
    ∀ m : ℕ, (m = 4 ∨ m = 5) →
    ∀ q : σ.QuadraticForms (Fin m), σ.IsNondegenerateQuadratic q →
      σ.quadraticWittIndex q = 1 →
      ∀ (S : GroupScheme (Spec (CommRingCat.of K))) (π : S ⟶ σ.isometryGroup q),
        σ.IsSpinCover q π →
      ∀ (e f : Fin m → D) (h : σ.IsHyperbolicPair q e f),
        ∃ (mu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S)
          (psi : CentralSimpleUnits.normOne K D ⟶ S), IsLeviLift h π mu psi

/-- **The kernel statement (Z).** In the setting of `LocalSpinKneserTitsStatement`, for every
spin cover `π`, hyperbolic pair `h` and lifts `(μ, ψ)` of the Levi morphism, the map
`z(u) = μ(u) ψ(u · 1)` is a bijection from `μ₂(A)` onto `ker π(A)` for every `K`-algebra `A`. -/
def SpinKernelGeneratorStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] (hD : Module.finrank K D = 4),
    ∀ σ : FirstKindInvolution K D, Module.finrank K σ.symmetricSubspace = 3 →
    ∀ m : ℕ, (m = 4 ∨ m = 5) →
    ∀ q : σ.QuadraticForms (Fin m), σ.IsNondegenerateQuadratic q →
      σ.quadraticWittIndex q = 1 →
      ∀ (S : GroupScheme (Spec (CommRingCat.of K))) (π : S ⟶ σ.isometryGroup q),
        σ.IsSpinCover q π →
      ∀ (e f : Fin m → D) (h : σ.IsHyperbolicPair q e f)
        (mu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S)
        (psi : CentralSimpleUnits.normOne K D ⟶ S), IsLeviLift h π mu psi →
        KernelGenerator (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hD) π mu psi

/-- **The rational kernel element is elementary.** In the setting of
`LocalSpinKneserTitsStatement`, for every spin cover `π`, hyperbolic pair `h` and lifts
`(μ, ψ)` of the Levi morphism, the rational point `z(-1) = μ(-1) ψ(-1)` of `S` lies in the
parabolic elementary subgroup `S(K)⁺`. -/
def SpinKernelElementaryLiftStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] (hD : Module.finrank K D = 4),
    ∀ σ : FirstKindInvolution K D, Module.finrank K σ.symmetricSubspace = 3 →
    ∀ m : ℕ, (m = 4 ∨ m = 5) →
    ∀ q : σ.QuadraticForms (Fin m), σ.IsNondegenerateQuadratic q →
      σ.quadraticWittIndex q = 1 →
      ∀ (S : GroupScheme (Spec (CommRingCat.of K))) (π : S ⟶ σ.isometryGroup q),
        σ.IsSpinCover q π →
      ∀ (e f : Fin m → D) (h : σ.IsHyperbolicPair q e f)
        (mu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S)
        (psi : CentralSimpleUnits.normOne K D ⟶ S), IsLeviLift h π mu psi →
        (GaloisPointComparison.rationalCoeffEquiv K S).symm
          (kernelPoint (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hD) mu psi _
            negOneRoot) ∈ parabolicElementarySubgroup S

/-- **Assembly.** The three spin-kernel statements imply `LocalSpinKneserTitsStatement`. -/
theorem localSpinKneserTits_of_spinKernel (h₁ : SpinLeviLiftStatement.{u})
    (h₂ : SpinKernelGeneratorStatement.{u}) (h₃ : SpinKernelElementaryLiftStatement.{u}) :
    LocalSpinKneserTitsStatement.{u} := by
  refine localSpinKneserTits_of_spinInputs ?_ ?_
  · intro K _ _ _ _ D _ _ _ _ hD σ hsym m hm q hq hw S π hπ e f h s a hsa
    obtain ⟨mu, psi, hl⟩ := h₁ K D hD σ hsym m hm q hq hw S π hπ e f h
    exact leviReducedNormSquare_of_kernelGenerator
      (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hD) hπ h hl
      (h₂ K D hD σ hsym m hm q hq hw S π hπ e f h mu psi hl) s a hsa
  · intro K _ _ _ _ D _ _ _ _ hD σ hsym m hm q hq hw S π hπ s hs
    obtain ⟨e, f, h⟩ := σ.exists_hyperbolicPair_of_quadraticWittIndex_pos q hq (by omega)
    obtain ⟨mu, psi, hl⟩ := h₁ K D hD σ hsym m hm q hq hw S π hπ e f h
    exact kernelElementary_of_kernelGenerator
      (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hD)
      (h₂ K D hD σ hsym m hm q hq hw S π hπ e f h mu psi hl)
      (h₃ K D hD σ hsym m hm q hq hw S π hπ e f h mu psi hl) s hs

end Langlands.GroupScheme.Quaternionic.SpinKernel
