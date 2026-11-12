import Langlands.Representation.Aubert.General.SameLeviPieceDisplacementStatement
import Langlands.Representation.LanglandsClassification.UnramifiedPieceDisplacement
import Langlands.Representation.LanglandsClassification.SimpleCorootFaceExistence
import Langlands.Representation.Plancherel.RationalRealParameterExtension
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.GroupScheme.Rational.ParabolicRootPresentationProof
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Strict displacement of the split component on non-identity same-Levi pieces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G P M : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- The unramified character of the Levi `M(F)` pulled back from a character
of the valuation image `M(F) → Hom(X^*(M)_F, ℤ)`. -/
def leviImageUnramifiedCharacter (l : M ⟶ P) (hl : IsRationalLeviSubgroup l)
    (χ : Plancherel.rationalImageCharacters M) : leviUnramifiedCharacters l hl :=
  letI := leviPointTopology l hl
  haveI := hl.isConnectedReductive.isAffineHom
  haveI : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  haveI := hl.isConnectedReductive.smooth
  Plancherel.rationalImageUnramifiedPullback M
    (Plancherel.continuous_rationalValuationImageProjection M) χ

theorem leviImageUnramifiedCharacter_apply (l : M ⟶ P) (hl : IsRationalLeviSubgroup l)
    (χ : Plancherel.rationalImageCharacters M) (g : rationalPoints M) :
    (leviImageUnramifiedCharacter l hl χ).val g =
      χ (Plancherel.rationalValuationImageProjection M g) := rfl

/-- Every point of the open coroot chamber of a root presentation is the real
part of an unramified character of the Levi pulled back from the valuation image. -/
theorem exists_imageUnramified_realPart_mem_chamber
    [LocallyOfFiniteType G.X.hom]
    (pres : ParabolicRootPresentation p l a) [Mono pres.data.i.hom.hom.left]
    (R : RelativeRootReflectionData pres.data.i) :
    ∃ χ : Plancherel.rationalImageCharacters M,
      leviUnramifiedRealPart l pres.isCompatible.levi a pres.isCompatible.splitComponent
          (leviImageUnramifiedCharacter l pres.isCompatible.levi χ) ∈
        restrictedCorootChamber pres.data.i pres.data.ν pres.data.J pres.data.f R := by
  have hT : IsSplitTorus pres.data.T.toGrp := pres.isCompatible.maximalSplit.isSplitSubtorus.1
  obtain ⟨y, hy⟩ := R.exists_mem_openSimpleCorootFace pres.data.i pres.data.ν hT
    (hT.finite_relativeRoots pres.data.i) pres.isCompatible.generic pres.data.J
    pres.isCompatible.subset_simpleRoots
  have hx : rationalCharacterRestrictReal (CommGroupScheme.groupHom pres.data.f) y ∈
      restrictedCorootChamber pres.data.i pres.data.ν pres.data.J pres.data.f R :=
    ⟨y, rfl, hy.1, hy.2⟩
  obtain ⟨χ, hχ⟩ := Plancherel.normalizedRealPart_imageCharacterPullback_surjective
    pres.isCompatible.splitComponent.isCentralSplitTorus.1.1 a
    pres.isCompatible.levi.isConnectedReductive pres.isCompatible.splitComponent
    (rationalCharacterRestrictReal (CommGroupScheme.groupHom pres.data.f) y)
  refine ⟨χ, ?_⟩
  have hχ' : Plancherel.SplitTorus.normalizedRealPart
      pres.isCompatible.splitComponent.isCentralSplitTorus.1.1
      ((Plancherel.rationalImageCharacterPullback M χ).comp (rationalPoints.map a)) =
      rationalCharacterRestrictReal (CommGroupScheme.groupHom pres.data.f) y := hχ
  change Plancherel.SplitTorus.normalizedRealPart _
    ((Plancherel.rationalImageCharacterPullback M χ).comp (rationalPoints.map a)) ∈ _
  rw [hχ']
  exact hx

/-- Proof of `SameLeviPieceStrictDisplacementStatement`: choose a root presentation,
reflection data and an unramified character whose real part lies in the open
coroot chamber. On a non-identity piece its real part moves by a nonzero cone
vector, so the valuation images of `a` and of the conjugate cannot agree
everywhere, because the character factors through the valuation image. -/
theorem sameLeviPieceStrictDisplacement : SameLeviPieceStrictDisplacementStatement.{u} := by
  intro k _ _ _ _ _ G hG _ _ P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hLevi
    A a ha z hz D b hb
  let := hG.isAffineHom
  have : LocallyOfFiniteType G.X.hom := by
    have := hG.smooth
    infer_instance
  obtain ⟨pres⟩ := parabolicRootPresentation.1 k G hG P M A p l a hp hl ha
  let := pres.isCompatible.maximalSplit.isSplitSubtorus.mono
  obtain ⟨R, -⟩ := relativeRootReflectionExistence k G hG pres.data.T pres.data.i
    pres.isCompatible.maximalSplit
  obtain ⟨χ, hψ⟩ := exists_imageUnramified_realPart_mem_chamber pres R
  let := leviPointTopology l hl
  set ψ : leviUnramifiedCharacters l hl := leviImageUnramifiedCharacter l hl χ with hψdef
  obtain ⟨δ, -, hδ0, hres⟩ :=
    D.normalizedRealPart_piece_eq_sub_nonzeroCone_of_nonidentity pres hLevi.symm hG R ψ hψ
      b hb hz
  by_contra hne
  push Not at hne
  apply hδ0
  have hcomp : ψ.val.toMonoidHom.comp (rationalPoints.map (b ≫ D.φ.hom ≫ D.l' ≫ D.p')) =
      ψ.val.toMonoidHom.comp (rationalPoints.map a) := by
    refine MonoidHom.ext fun t => ?_
    change (leviImageUnramifiedCharacter l hl χ).val _ =
      (leviImageUnramifiedCharacter l hl χ).val _
    rw [leviImageUnramifiedCharacter_apply, leviImageUnramifiedCharacter_apply, hne t]
  rw [hcomp] at hres
  have hres' : leviUnramifiedRealPart l hl a pres.isCompatible.splitComponent ψ =
      leviUnramifiedRealPart l hl a pres.isCompatible.splitComponent ψ - δ := hres
  exact (sub_eq_self.mp hres'.symm)

end Langlands.Aubert.General.RepresentedParabolic
