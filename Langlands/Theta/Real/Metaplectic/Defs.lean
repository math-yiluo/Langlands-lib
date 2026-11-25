import Langlands.Theta.Real.LocalLift

/-!
# The real metaplectic group

For a finite type `l`, `RealMetaplecticGroup l` is the group of triples `(s, U, V)` where
`s ∈ Sp_{2l}(ℝ) = Matrix.symplecticGroup l ℝ`, `U` is a unitary operator of `L²(ℝˡ)` and `V` an
invertible operator of Schwartz space, such that

* `U` extends `V`: `U (f ∈ L²) = V f` for Schwartz functions `f`;
* `U` carries the Schrödinger operator of `w` to that of `s w`:
  `U ∘ schrodingerL2 w = schrodingerL2 (s w) ∘ U`, and `V` does the same with the derived operators
  `schrodingerDeriv`;
* `V` is normalized on vacuum vectors (`IsNormalizedLift s V`): for every symplectic `s'` and every
  vacuum vector `f` of `s'`, `(V f)(0)² · det(A - iB)(s s') = f(0)² · det(A - iB)(s')`.

The group law is componentwise; `proj`, `weil`, `weilSchwartz` are the three projections. The
topology is induced by `g ↦ (proj g, (f ↦ weil g f))`, with the pointwise topology on maps of `L²`.

What is proved about it (`Langlands.Theta.Real.Metaplectic.Basic`, `Covering`, `Smooth`,
`Gaussian`): it is a Hausdorff topological group, `proj` is a surjective covering map with kernel
`{1, negOne}`, `weil negOne = -1`, `weil` is strongly continuous and normalizes the Schrödinger
representation, and its Schwartz vectors are smooth. What is **not** proved: that the cover does
not split, that is, that `RealMetaplecticGroup l` is connected and not isomorphic to
`Sp_{2l}(ℝ) × {±1}`. The name "metaplectic group" is justified by the construction (the
operators `U` are the operators of the Weil representation, unique up to sign by the Schur lemma
`Intertwines.exists_eq_smul`), not yet by a theorem.

The vacuum condition: `f` is a vacuum vector of `s` (`IsVacuumFor s f`) if
`D(s eⱼ) f = i D(s e_{l+j}) f` for all `j`, where `D = schrodingerDeriv`; for `s = 1` the vacuum
vectors are the multiples of the Gaussian.
-/

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix Filter Topology FourierTransform
open scoped Real ContDiff

namespace Langlands.Theta

open Langlands.Theta.Real.Internal

variable {l : Type} [Fintype l] [DecidableEq l]
open Langlands.Theta.Real

namespace Real

/-- `A - iB` for `s = [[A, B], [C, D]]`. -/
def automorphyUpper (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) : Matrix l l ℂ :=
  fun a b => (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)

/-- `C - iD` for `s = [[A, B], [C, D]]`. -/
def automorphyLower (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) : Matrix l l ℂ :=
  fun a b => (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)

/-- The automorphy determinant `det (A - iB)`. -/
def automorphyDet (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) : ℂ := (automorphyUpper s).det

/-- `f` is a vacuum vector of `s`: `D(s eⱼ) f = i D(s e_{l+j}) f` for all `j`. -/
def IsVacuumFor (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (f : RealSchwartz l) : Prop :=
  ∀ j : l, schrodingerDeriv (s *ᵥ Pi.single (.inl j) 1) f =
    I • schrodingerDeriv (s *ᵥ Pi.single (.inr j) 1) f

/-- `U` is normalized over `s`: `(U f)(0)² det (A - iB)(s s') = f(0)² det (A - iB)(s')` for every
symplectic `s'` and vacuum vector `f` of `s'`. -/
def IsNormalizedLift (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (U : RealSchwartz l →L[ℂ] RealSchwartz l) :
    Prop :=
  ∀ s' : Matrix.symplecticGroup l ℝ, ∀ f : RealSchwartz l, IsVacuumFor s'.1 f →
    (U f 0) ^ 2 * automorphyDet (s * s'.1) = (f 0) ^ 2 * automorphyDet s'.1

/-- An operator carrying the derived operators along `s` carries vacuum vectors of `s'` to vacuum
vectors of `s s'`. -/
theorem IsVacuumFor.map {s s' : Matrix (l ⊕ l) (l ⊕ l) ℝ} {U : RealSchwartz l →L[ℂ] RealSchwartz l}
    (h : ∀ w f, U (schrodingerDeriv w f) = schrodingerDeriv (s *ᵥ w) (U f)) {f : RealSchwartz l}
    (hf : IsVacuumFor s' f) : IsVacuumFor (s * s') (U f) := fun j => by
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← h, ← h, hf j, map_smul]

end Real

namespace RealMetaplecticGroup

variable (l) in
/-- The ambient group of triples (internal). -/
abbrev Ambient : Type :=
  Matrix.symplecticGroup l ℝ × (RealL2 l ≃ₗᵢ[ℂ] RealL2 l) × (RealSchwartz l →L[ℂ] RealSchwartz l)ˣ

/-- The conditions on a triple (internal). -/
structure Mem (x : Ambient l) : Prop where
  compat : ∀ f, x.2.1 (schwartzToL2 l f) = schwartzToL2 l (x.2.2.1 f)
  comm_schrodingerL2 : ∀ w f, x.2.1 (schrodingerL2 w f) = schrodingerL2 (x.1.1 *ᵥ w) (x.2.1 f)
  comm_schrodingerDeriv : ∀ w f,
    x.2.2.1 (schrodingerDeriv w f) = schrodingerDeriv (x.1.1 *ᵥ w) (x.2.2.1 f)
  isNormalizedLift : IsNormalizedLift x.1.1 x.2.2.1

variable (l) in
/-- The subgroup of triples (internal). -/
def subgroup : Subgroup (Ambient l) where
  carrier := {x | Mem x}
  one_mem' := ⟨fun _ => rfl, fun w f => by simp, fun w f => by simp, fun s' f _ => by simp⟩
  mul_mem' {x y} hx hy :=
    ⟨fun f => (congrArg x.2.1 (hy.compat f)).trans (hx.compat _),
     fun w f => by
      show x.2.1 (y.2.1 (schrodingerL2 w f)) = schrodingerL2 ((x.1.1 * y.1.1) *ᵥ w) (x.2.1 (y.2.1 f))
      rw [hy.comm_schrodingerL2, hx.comm_schrodingerL2, mulVec_mulVec],
     fun w f => by
      show x.2.2.1 (y.2.2.1 (schrodingerDeriv w f)) =
        schrodingerDeriv ((x.1.1 * y.1.1) *ᵥ w) (x.2.2.1 (y.2.2.1 f))
      rw [hy.comm_schrodingerDeriv, hx.comm_schrodingerDeriv, mulVec_mulVec],
     fun s' f hf => by
      have h1 := hx.isNormalizedLift (y.1 * s') (y.2.2.1 f) (hf.map hy.comm_schrodingerDeriv)
      have h2 := hy.isNormalizedLift s' f hf
      show (x.2.2.1 (y.2.2.1 f) 0) ^ 2 * automorphyDet (x.1.1 * y.1.1 * s'.1) = _
      rw [Matrix.mul_assoc]
      exact h1.trans h2⟩
  inv_mem' {x} hx := by
    have e1 : ∀ f, x.2.2.1 (x.2.2⁻¹.1 f) = f := fun f => by
      rw [← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]
    have e2 : ∀ f, x.2.2⁻¹.1 (x.2.2.1 f) = f := fun f => by
      rw [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]
    have e3 : x.1.1 * x.1⁻¹.1 = 1 := congrArg Subtype.val (mul_inv_cancel x.1)
    have hd : ∀ w f, x.2.2⁻¹.1 (schrodingerDeriv w f) =
        schrodingerDeriv (x.1⁻¹.1 *ᵥ w) (x.2.2⁻¹.1 f) := fun w f => by
      have := hx.comm_schrodingerDeriv (x.1⁻¹.1 *ᵥ w) (x.2.2⁻¹.1 f)
      rw [mulVec_mulVec, e3, one_mulVec, e1] at this
      rw [← this, e2]
    refine ⟨fun f => ?_, fun w f => ?_, hd, fun s' f hf => ?_⟩
    · show x.2.1.symm _ = schwartzToL2 l (x.2.2⁻¹.1 f)
      rw [LinearIsometryEquiv.symm_apply_eq, hx.compat, e1]
    · show x.2.1.symm _ = schrodingerL2 (x.1⁻¹.1 *ᵥ w) (x.2.1.symm f)
      rw [LinearIsometryEquiv.symm_apply_eq, hx.comm_schrodingerL2, mulVec_mulVec, e3, one_mulVec,
        LinearIsometryEquiv.apply_symm_apply]
    · have h1 := hx.isNormalizedLift (x.1⁻¹ * s') (x.2.2⁻¹.1 f) (hf.map hd)
      rw [e1, show (x.1⁻¹ * s').1 = x.1⁻¹.1 * s'.1 from rfl, ← Matrix.mul_assoc, e3,
        Matrix.one_mul] at h1
      exact h1.symm

end RealMetaplecticGroup

variable (l) in
/-- The metaplectic group of `ℝ^{2l}`: the triples `(s, U, V)` of a symplectic matrix, a unitary
operator of `L²` and an invertible operator of Schwartz space such that `U` extends `V`, `U` and
`V` carry the Schrödinger operators and their derivatives of `w` to those of `s w`, and `V` is
normalized on vacuum vectors. -/
def RealMetaplecticGroup : Type := RealMetaplecticGroup.subgroup l

namespace RealMetaplecticGroup

/-- The group structure: the componentwise product of triples. -/
instance : Group (RealMetaplecticGroup l) := inferInstanceAs (Group (subgroup l))

/-- The projection to `Sp_{2l}(ℝ)`. -/
def proj : RealMetaplecticGroup l →* Matrix.symplecticGroup l ℝ :=
  (MonoidHom.fst _ _).comp (subgroup l).subtype

/-- The Weil representation on `L²(ℝˡ)`. -/
def weil : RealMetaplecticGroup l →* (RealL2 l ≃ₗᵢ[ℂ] RealL2 l) :=
  (MonoidHom.fst _ _).comp ((MonoidHom.snd _ _).comp (subgroup l).subtype)

/-- The Weil representation on Schwartz space. -/
def weilSchwartz : RealMetaplecticGroup l →* (RealSchwartz l →L[ℂ] RealSchwartz l) :=
  (Units.coeHom _).comp ((MonoidHom.snd _ _).comp ((MonoidHom.snd _ _).comp (subgroup l).subtype))

/-- The conditions on the triple of an element (internal). -/
theorem mem (g : RealMetaplecticGroup l) : Mem (Subtype.val (p := (· ∈ subgroup l)) g) :=
  Subtype.property (p := (· ∈ subgroup l)) g

/-- On Schwartz functions the operator of `L²` is the operator of Schwartz space. -/
theorem weil_toLp (g : RealMetaplecticGroup l) (f : RealSchwartz l) :
    weil g (f.toLp 2) = (weilSchwartz g f).toLp 2 :=
  (mem g).compat f

/-- The Weil representation normalizes the Schrödinger representation:
`weil g ∘ schrodingerL2 w = schrodingerL2 (proj g w) ∘ weil g`. -/
theorem weil_schrodingerL2 (g : RealMetaplecticGroup l) (w : l ⊕ l → ℝ) (f : RealL2 l) :
    weil g (schrodingerL2 w f) = schrodingerL2 ((proj g).1 *ᵥ w) (weil g f) :=
  (mem g).comm_schrodingerL2 w f

/-- The Weil representation on Schwartz space normalizes the derived Schrödinger
representation. -/
theorem weilSchwartz_schrodingerDeriv (g : RealMetaplecticGroup l) (w : l ⊕ l → ℝ)
    (f : RealSchwartz l) :
    weilSchwartz g (schrodingerDeriv w f) = schrodingerDeriv ((proj g).1 *ᵥ w) (weilSchwartz g f) :=
  (mem g).comm_schrodingerDeriv w f

/-- The Schwartz operator of an element is normalized on vacuum vectors. -/
theorem isNormalizedLift_weilSchwartz (g : RealMetaplecticGroup l) :
    IsNormalizedLift (proj g).1 (weilSchwartz g) :=
  (mem g).isNormalizedLift

/-- The topology induced by `g ↦ (proj g, (f ↦ weil g f))`. -/
instance : TopologicalSpace (RealMetaplecticGroup l) :=
  TopologicalSpace.induced (fun g => ((proj g, fun f => weil g f) :
    Matrix.symplecticGroup l ℝ × (RealL2 l → RealL2 l))) inferInstance

/-- The map defining the topology is continuous (internal). -/
theorem continuous_pair : Continuous fun g : RealMetaplecticGroup l =>
    ((proj g, fun f => weil g f) : Matrix.symplecticGroup l ℝ × (RealL2 l → RealL2 l)) :=
  continuous_induced_dom

/-- The projection is continuous. -/
theorem continuous_proj : Continuous (proj : RealMetaplecticGroup l → Matrix.symplecticGroup l ℝ) :=
  (continuous_pair (l := l)).fst

/-- Strong continuity of the Weil representation. -/
theorem continuous_weil (f : RealL2 l) : Continuous fun g : RealMetaplecticGroup l => weil g f :=
  (continuous_apply f).comp (continuous_pair (l := l)).snd

end RealMetaplecticGroup

namespace Real

/-- The explicit operator over a matrix of the big cell `det A ≠ 0`:
`bigCellOp A⁻¹ B C |det A|^{-1/2}` for `g = [[A, B], [C, D]]`. -/
def bigCellSection (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) : RealSchwartz l →L[ℂ] RealSchwartz l :=
  bigCellOp (Ring.inverse (blockCLM Sum.inl Sum.inl g)) (blockCLM Sum.inl Sum.inr g)
    (blockCLM Sum.inr Sum.inl g) (√|g.toBlocks₁₁.det|)⁻¹

namespace Internal

/-- The derivative of `bigCellSection` at `1` in the direction `X` (internal). -/
def bigCellSectionDeriv (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (f : RealSchwartz l) : RealSchwartz l :=
  quadMul (blockCLM Sum.inr Sum.inl X) f + vectorFieldDeriv (-blockCLM Sum.inl Sum.inl X) f +
    fourierCLM ℂ (RealSchwartz l) (quadMul (-blockCLM Sum.inl Sum.inr X) (fourierInvCLM ℂ (RealSchwartz l) f)) -
    ((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) • f

end Internal

end Real

end Langlands.Theta
