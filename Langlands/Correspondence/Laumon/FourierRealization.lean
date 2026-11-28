import Langlands.MathlibBase
import Langlands.Correspondence.Laumon.Traits
import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedFourierKernelBounded
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
import WeilConjectures.WeilSheaf.Fourier
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineOver
import WeilConjectures.WeilSheaf.CondensedModelBoundedConstructible
import WeilConjectures.WeilSheaf.CondensedModelWeilDerived
import WeilConjectures.WeilSheaf.SmoothPurityNativeDescent
import WeilConjectures.WeilSheaf.OpenImmersion
import WeilConjectures.WeilSheaf.FourierInversion.Reflection
import WeilConjectures.SmoothPurity.TateTwistBoundedConstructible

/-!
# Laumon's arithmetic Fourier transform on the affine line over a finite field

For a finite field `k`, a prime `ℓ ≠ char k` and a character `ψ : k → ℚ̄_ℓ`, this module builds
the arithmetic Fourier–Deligne transform `FTψ(K) = Rpr'_!(pr^*K ⊗ Lψ(xx'))[1]` of Laumon 1987,
(1.2.1.1), on bounded constructible `ℚ̄_ℓ`-complexes of the pro-étale site of `A = 𝔸¹_k`, from the
operations of weil-conjectures, and states its comparison with the ambient condensed transform,
its form over the compactified target, its comparison with the Weil transform on the geometric
fibre, its fibres at rational points, its compatibility with finite extension of the constant
field, the composite kernel and the inversion formula (Laumon (1.2.2.1)–(1.2.2.9), (1.2.3.1)).
The statements are not proved here.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

-- Two global instances of weil-conjectures are not the ones its six operations are stated with:
-- the monoidal structure `sfbRegularAbMonoidal` on abelian sheaves (for which
-- `Profinite.padicAlgClRingObj ℓ` is not a ring object), and the derived category instance
-- `CompletedCoefficientPushforward.hasDerived` (which has the wrong morphism universe).
attribute [-instance] CategoryTheory.sfbRegularAbMonoidal
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.hasDerived

namespace Langlands.Henniart.Laumon

section Setting

variable (k : Type u) [Field k]

/-- The affine line `A = 𝔸¹_k` (and its dual `A'`) as an object of `Over (Spec k)`. -/
def fourierLine : Over (Spec (.of k)) :=
  Over.mk (affineLine k ↘ Spec (.of k))

instance : LocallyOfFiniteType (fourierLine k).hom :=
  inferInstanceAs (LocallyOfFiniteType (affineLine k ↘ Spec (.of k)))

instance : QuasiCompact (fourierLine k).hom :=
  inferInstanceAs (QuasiCompact (affineLine k ↘ Spec (.of k)))

instance : IsSeparated (fourierLine k).hom :=
  inferInstanceAs (IsSeparated (affineLine k ↘ Spec (.of k)))

instance : LocallyOfFiniteType ((fourierLine k).left ↘ Spec (.of k)) :=
  inferInstanceAs (LocallyOfFiniteType (affineLine k ↘ Spec (.of k)))

instance : QuasiCompact ((fourierLine k).left ↘ Spec (.of k)) :=
  inferInstanceAs (QuasiCompact (affineLine k ↘ Spec (.of k)))

instance : QuasiSeparated ((fourierLine k).left ↘ Spec (.of k)) :=
  inferInstanceAs (QuasiSeparated (affineLine k ↘ Spec (.of k)))

/-- The product `A × A'` as an object of `Over (Spec k)`. -/
def fourierPlane : Over (Spec (.of k)) :=
  Over.mk (affinePlane k ↘ Spec (.of k))

instance : LocallyOfFiniteType (fourierPlane k).hom :=
  inferInstanceAs (LocallyOfFiniteType (affinePlane k ↘ Spec (.of k)))

instance : QuasiCompact (fourierPlane k).hom := by
  have : QuasiCompact (pullback.fst (affineLine k ↘ Spec (.of k)) (affineLine k ↘ Spec (.of k))) :=
    inferInstance
  exact inferInstanceAs (QuasiCompact (pullback.fst (affineLine k ↘ Spec (.of k))
    (affineLine k ↘ Spec (.of k)) ≫ affineLine k ↘ Spec (.of k)))

instance : IsSeparated (fourierPlane k).hom := by
  have : IsSeparated (pullback.fst (affineLine k ↘ Spec (.of k)) (affineLine k ↘ Spec (.of k))) :=
    inferInstance
  exact inferInstanceAs (IsSeparated (pullback.fst (affineLine k ↘ Spec (.of k))
    (affineLine k ↘ Spec (.of k)) ≫ affineLine k ↘ Spec (.of k)))

/-- The first projection `pr : A × A' → A`. -/
def fourierFirstProjection : fourierPlane k ⟶ fourierLine k :=
  Over.homMk (affinePlane.fst k)
    (inferInstance : (affinePlane.fst k).IsOver (Spec (.of k))).comp_over

/-- The second projection `pr' : A × A' → A'`. -/
def fourierSecondProjection : fourierPlane k ⟶ fourierLine k :=
  Over.homMk (affinePlane.snd k)
    (inferInstance : (affinePlane.snd k).IsOver (Spec (.of k))).comp_over

/-- The isomorphism of `A × A'` with the relative affine line `𝔸¹_{A'}` over `A'`. -/
def fourierPlaneIsoRelativeLine : affinePlane k ≅ AffineSpace PUnit.{u + 1} (affineLine k) :=
  (AffineSpace.isPullback_map (n := PUnit.{u + 1}) (affineLine k ↘ Spec (.of k))).isoPullback.symm

/-- The compactification `A × A' ↪ D × A' → A'` of the second projection. -/
def fourierProjectionCompactification : Compactification (fourierSecondProjection k).left :=
  ((affineTraceLineCompactification (affineLine k)).precomp
    (fourierPlaneIsoRelativeLine k).hom).copy
    (IsPullback.isoPullback_inv_snd _).symm

end Setting

section Transform

variable (k : Type u) [Field k] [Fintype k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]

/-- A character `ψ : k → E` with values in the constant global sections of the condensed
coefficient ring `Λ = ℚ̲̄_ℓ`, through `Profinite.PadicAlgCl.constRingHom`. -/
def condensedFourierCharacter (ψ : AddChar k (PadicAlgCl ℓ)) :
    AddChar k (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)) :=
  (Profinite.PadicAlgCl.constRingHom.{u} ℓ).toMonoidHom.compAddChar ψ

omit [Fintype k] [Fact ℓ.Prime] in
/-- The prime `ℓ` differs from `p`. -/
theorem prime_ne_ringChar : ℓ ≠ ringChar k := fun h => (Fact.out : ringChar k ≠ ℓ) h.symm

omit [Fact (ringChar k ≠ ℓ)] in
/-- The characteristic `p` of `k` is invertible in the constant sections of `Λ`. -/
theorem isUnit_ringChar_condensed :
    IsUnit ((ringChar k : ℕ) : MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)) := by
  have h : ((ringChar k : ℕ) : PadicAlgCl ℓ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Fact.out : (ringChar k).Prime).ne_zero
  simpa using (isUnit_iff_ne_zero.2 h).map (Profinite.PadicAlgCl.constRingHom.{u} ℓ)

/-- The arithmetic Fourier kernel `Lψ(xx')` on `A × A'`: weil-conjectures'
`condensedFourierKernel` for the standard pairing, placed in degree `0`, as a bounded
constructible complex. -/
def arithmeticFourierKernel (ψ : AddChar k (PadicAlgCl ℓ)) :
    Dᵇc((fourierPlane k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  letI : (pullback (affineLine k ↘ Spec (.of k)) (affineLine k ↘ Spec (.of k))).Over
      (Spec (.of k)) :=
    ⟨pullback.fst _ _ ≫ affineLine k ↘ Spec (.of k)⟩
  letI : (Spec (.of k)).Over (Spec (.of k)) := ⟨𝟙 _⟩
  ⟨(DerivedCategory.singleFunctor _ 0).obj
      (condensedFourierKernel (Profinite.padicAlgClRingObj ℓ) k (affineLine k ↘ Spec (.of k))
        (affineLine k ↘ Spec (.of k))
        (condensedFourierCharacter k ℓ ψ) (AffineSpace.stdPairing PUnit.{u + 1} (Spec (.of k)))),
    condensedFourierKernel_boundedConstructible (Profinite.padicAlgClRingObj ℓ) (ringChar k)
      ⟨ℓ, inferInstance, prime_ne_ringChar k ℓ, Or.inr (Or.inr ⟨Iso.refl _⟩)⟩
      (isUnit_ringChar_condensed k ℓ) k (Or.inl inferInstance) k _ _ _ _⟩

/-- **Laumon's arithmetic Fourier transform** `FTψ(K) = Rpr'_!(pr^*K ⊗ Lψ(xx'))[1]` on bounded
constructible `ℚ̄_ℓ`-complexes on `A = 𝔸¹_k` (Laumon (1.2.1.1)), with `Rpr'_!` computed with the
compactification `fourierProjectionCompactification k`. -/
def boundedConstructibleArithmeticFourier (ψ : AddChar k (PadicAlgCl ℓ)) :
    Dᵇc((fourierLine k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((fourierLine k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (fourierFirstProjection k) ⋙
    tensorRight (arithmeticFourierKernel k ℓ ψ) ⋙
    boundedConstructibleLowerShriekOfCompactification ℓ (f := fourierSecondProjection k)
      (fourierProjectionCompactification k) ⋙
    shiftFunctor _ (1 : ℤ)

/-- The ambient arithmetic Fourier transform: weil-conjectures'
`condensedFieldFourierTransform` on the whole derived category of `Λ`-modules on `A`, for the
character `condensedFourierCharacter k ℓ ψ` and the compactification
`fourierProjectionCompactification k`. -/
abbrev ambientArithmeticFourier (ψ : AddChar k (PadicAlgCl ℓ)) :=
  condensedFieldFourierTransform (Profinite.padicAlgClRingObj ℓ) k k
    (condensedFourierCharacter k ℓ ψ) (fourierProjectionCompactification k)

end Transform

/-- **Restriction of the arithmetic Fourier transform** (Laumon (1.2.1.1), p. 141, and
(2.3.3.1), p. 161). For every finite field `k`, prime `ℓ ≠ char k` and character
`ψ : k → ℚ̄_ℓ`, the ambient transform `ambientArithmeticFourier k ℓ ψ` carries bounded
constructible complexes to bounded constructible complexes, `boundedConstructibleArithmeticFourier`
is its restriction to them, and the same holds on inputs extended by zero from an open
`j : U ↪ A`, the ambient extension by zero being the compact support pushforward for the
compactification of `j` with identity proper part. -/
def ArithmeticFourierRestrictionStatement : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (ψ : AddChar k (PadicAlgCl ℓ)),
    (∀ K : Dᵇc((fourierLine k).left)⟦Profinite.padicAlgClRingObj ℓ⟧,
      boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (fourierLine k).left)
        ((ambientArithmeticFourier k ℓ ψ).obj K.obj)) ∧
    Nonempty (boundedConstructibleArithmeticFourier k ℓ ψ ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ ambientArithmeticFourier k ℓ ψ) ∧
    ∀ (U : Over (Spec (.of k))) [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
      [IsSeparated U.hom] (j : U ⟶ fourierLine k) [IsOpenImmersion j.left],
      Nonempty (boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
          boundedConstructibleArithmeticFourier k ℓ ψ ⋙ (boundedConstructible _).ι ≅
        (boundedConstructible _).ι ⋙
          rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ)
            (Compactification.ofIsOpenImmersion j.left) ⋙
          ambientArithmeticFourier k ℓ ψ)

section CompactifiedTarget

variable (k : Type u) [Field k]

/-- The base `Spec k` as an object of `Over (Spec k)`. -/
def fourierBase : Over (Spec (.of k)) :=
  Over.mk (𝟙 (Spec (.of k)))

instance : LocallyOfFiniteType (fourierBase k).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))

instance : QuasiCompact (fourierBase k).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))

instance : IsSeparated (fourierBase k).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))

/-- The projective completion `D'` of the dual line, the projective line over `Spec k`. -/
def fourierDualCompletion : Over (Spec (.of k)) :=
  Scheme.overProjectiveLine (fourierBase k)

instance : LocallyOfFiniteType (fourierDualCompletion k).hom :=
  inferInstanceAs (LocallyOfFiniteType (Scheme.overProjectiveLine (fourierBase k)).hom)

instance : QuasiCompact (fourierDualCompletion k).hom :=
  inferInstanceAs (QuasiCompact (Scheme.overProjectiveLine (fourierBase k)).hom)

instance : IsSeparated (fourierDualCompletion k).hom :=
  inferInstanceAs (IsSeparated (Scheme.overProjectiveLine (fourierBase k)).hom)

/-- The open immersion `A' ↪ D'`, the standard affine chart `x' ↦ [x' : 1]` of the projective
line, with complement the point `∞'`. -/
def fourierDualChart : fourierLine k ⟶ fourierDualCompletion k :=
  Over.homMk (ProjectiveLine.affineChart (Spec (.of k))) (by
    change ProjectiveLine.affineChart (Spec (.of k)) ≫
      (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫ 𝟙 (Spec (.of k)) = _
    rw [Category.comp_id]
    exact ProjectiveLine.affineChart_over (Spec (.of k)))

instance : IsOpenImmersion (fourierDualChart k).left :=
  inferInstanceAs (IsOpenImmersion (ProjectiveLine.affineChart (Spec (.of k))))

/-- The open immersion `D × A' ↪ D × D'` of the projective lines over `A'` and over `D'`, the
base change of `fourierDualChart k`; its source is the scheme of the compactification
`fourierProjectionCompactification k`. -/
def fourierCompletionChart :
    (fourierProjectionCompactification k).overObj (f := fourierSecondProjection k) ⟶
      Scheme.overProjectiveLine (fourierDualCompletion k) :=
  Over.homMk (Scheme.overProjectiveLineMap (fourierDualChart k)).left
    (Scheme.overProjectiveLineMap (fourierDualChart k)).w

instance : IsOpenImmersion (fourierCompletionChart k).left :=
  MorphismProperty.of_isPullback (Scheme.isPullback_overProjectiveLineMap (fourierDualChart k)).flip
    (inferInstanceAs (IsOpenImmersion (ProjectiveLine.affineChart (Spec (.of k)))))

end CompactifiedTarget

section CompactifiedKernel

variable (k : Type u) [Field k] [Fintype k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]

/-- The complex `B_K` of Laumon (2.3.2.1)(iii) on `D × A'`: `pr^*K ⊗ Lψ(xx')` on `A × A'`,
extended by zero along the open immersion of the compactification
`fourierProjectionCompactification k`, functorially in `K`. -/
def fourierKernelZeroExtension (ψ : AddChar k (PadicAlgCl ℓ)) :
    Dᵇc((fourierLine k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(((fourierProjectionCompactification k).overObj
        (f := fourierSecondProjection k)).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (fourierFirstProjection k) ⋙
    tensorRight (arithmeticFourierKernel k ℓ ψ) ⋙
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
      ((fourierProjectionCompactification k).overI (f := fourierSecondProjection k))

/-- The complex `B̄_K` on `D × D'`: `B_K` extended by zero along `D × A' ↪ D × D'`,
functorially in `K`. -/
def extendedFourierKernel (ψ : AddChar k (PadicAlgCl ℓ)) :
    Dᵇc((fourierLine k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((Scheme.overProjectiveLine (fourierDualCompletion k)).left)⟦
        Profinite.padicAlgClRingObj ℓ⟧ :=
  fourierKernelZeroExtension k ℓ ψ ⋙
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
      (fourierCompletionChart k)

end CompactifiedKernel

/-- **The transform over the compactified target** (Laumon (2.3.2.1)(iii), p. 160, and
(2.3.3.1)(iii), p. 161). With `q̄ : D × D' → D'` the projection, `Rq̄_* B̄_K[1]` restricts on
`A'` to the arithmetic transform of `K`, and it is the extension by zero of that transform
across `∞'`, functorially in `K`. -/
def ArithmeticFourierCompactifiedTargetStatement : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (ψ : AddChar k (PadicAlgCl ℓ)),
    Nonempty (extendedFourierKernel k ℓ ψ ⋙
        boundedConstructibleLowerStarOfIsProper ℓ
          (Scheme.overProjectiveLineProj (fourierDualCompletion k)) ⋙
        shiftFunctor _ (1 : ℤ) ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (fourierDualChart k) ≅
      boundedConstructibleArithmeticFourier k ℓ ψ) ∧
    Nonempty (extendedFourierKernel k ℓ ψ ⋙
        boundedConstructibleLowerStarOfIsProper ℓ
          (Scheme.overProjectiveLineProj (fourierDualCompletion k)) ⋙
        shiftFunctor _ (1 : ℤ) ≅
      boundedConstructibleArithmeticFourier k ℓ ψ ⋙
        boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (fourierDualChart k))

section WeilRealization

variable (k : Type u) [Field k] [Fintype k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]

/-- The Weil realization of bounded constructible arithmetic complexes on a separated
finite-type `k`-scheme. This is `WeilComplex.finiteBaseNativeDescent`, the pullback to the
geometric fibre with its canonical Frobenius structure. -/
def weilRealization (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ WeilComplex k ℓ X.left :=
  letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  letI : IsSeparated (X.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated X.hom)
  letI : LocallyOfFiniteType (X.left ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.hom)
  letI : QuasiCompact (X.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact X.hom)
  WeilComplex.finiteBaseNativeDescent (k₀ := k) (l := ℓ) (X := X.left)

/-- The target `(-1) ⋙ [-2] ⋙ a^* ⋙ [1] ⋙ [1]` of weil-conjectures' Weil inversion
`AlgebraicGeometry.nonempty_iso_fourierTransform_comp_self`, with `a(x) = -x`. -/
def weilInversionTarget : WeilComplex k ℓ (affineLine k) ⥤ WeilComplex k ℓ (affineLine k) :=
  WeilComplex.tateTwist k ℓ (affineLine k) (-1) ⋙ shiftFunctor _ (-2 : ℤ) ⋙
    WeilComplex.upperStar (affineLine.neg k) ⋙ shiftFunctor _ (1 : ℤ) ⋙ shiftFunctor _ (1 : ℤ)

/-- The linear function `x ↦ a x` on the affine line. -/
def linearFunction (a : k) : Γ(affineLine k, ⊤) :=
  (affineLine k ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv.hom a) *
    AffineSpace.coord (Spec (.of k)) PUnit.unit

end WeilRealization

/-- The comparison `(F ⋙ F) ⋙ R ≅ R ⋙ (G ⋙ G)` obtained by applying a comparison
`e : F ⋙ R ≅ R ⋙ G` twice. -/
def commIsoTwice {C D : Type*} [Category C] [Category D] {F : C ⥤ C} {G : D ⥤ D} {R : C ⥤ D}
    (e : F ⋙ R ≅ R ⋙ G) : (F ⋙ F) ⋙ R ≅ R ⋙ (G ⋙ G) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F e ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e G ≪≫ Functor.associator _ _ _

/-- **The arithmetic Artin–Schreier lines and their Weil realizations** (Laumon (1.1.3.2),
p. 139, and (1.2.1.1), p. 141). For every `a ∈ k`, the geometric fibre with its Frobenius
structure of the arithmetic Artin–Schreier sheaf `Lψ(ax)` on `A` (weil-conjectures'
`condensedArtinSchreierSheafOf` for the function `a x`) is isomorphic, as a condensed Weil
object, to the condensed model of the Weil Artin–Schreier sheaf
`AlgebraicGeometry.artinSchreier ψ a`. -/
def ArithmeticArtinSchreierWeilComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (ψ : AddChar k (PadicAlgCl ℓ)) (a : k),
    Nonempty ((geometricFiberWeilLowerStar (Profinite.padicAlgClRingObj ℓ)
        (affineLine k ↘ Spec (.of k))).obj
        (condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k (affineLine k)
          (condensedFourierCharacter k ℓ ψ) (linearFunction k a)) ≅
      (ProEtaleWeilSheaf.toCondensed k ℓ (affineLine k)).obj
        ((WeilSheaf.objectProperty k ℓ (affineLine k)).ι.obj (artinSchreier ψ a)))

/-- **The arithmetic transform and the Weil transform** (Laumon (1.2.1.1), p. 141, (1.2.2.9),
p. 144, and (2.4.2), pp. 162–163). Weil realization commutes with the Fourier transform, the
shift `[1]` and extension by zero along each open immersion `j : U ↪ A`. For the shifted
zero-extended input `j_! K[1]`, the comparison is the composite of these three natural
isomorphisms. -/
def ArithmeticFourierWeilComparisonStatement : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (ψ : AddChar k (PadicAlgCl ℓ)),
    let R := weilRealization k ℓ (fourierLine k)
    let F := boundedConstructibleArithmeticFourier k ℓ ψ
    let G := fourierTransform ψ
    ∃ (e : F ⋙ R ≅ R ⋙ G)
      (s : shiftFunctor _ (1 : ℤ) ⋙ R ≅ R ⋙ shiftFunctor _ (1 : ℤ)),
      ∀ (U : Over (Spec (.of k))) [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
        [IsSeparated U.hom] (j : U ⟶ fourierLine k) [IsOpenImmersion j.left]
        [QuasiCompact j.left],
        let J := boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j
        let J' := WeilComplex.derivedLowerShriek k ℓ j.left
        let Rᵤ := weilRealization k ℓ U
        ∃ z : J ⋙ R ≅ Rᵤ ⋙ J',
          ∃ c : J ⋙ shiftFunctor _ (1 : ℤ) ⋙ F ⋙ R ≅ Rᵤ ⋙ J' ⋙ shiftFunctor _ (1 : ℤ) ⋙ G,
            c = Functor.isoWhiskerLeft (J ⋙ shiftFunctor _ (1 : ℤ)) e ≪≫
              Functor.isoWhiskerLeft J (Functor.isoWhiskerRight s G) ≪≫
              Functor.isoWhiskerRight z (shiftFunctor _ (1 : ℤ) ⋙ G)

section Fibre

variable (k : Type u) [Field k]

/-- The structure morphism `A → Spec k` in `Over (Spec k)`. -/
def fourierLineStructure : fourierLine k ⟶ fourierBase k :=
  Over.homMk (affineLine k ↘ Spec (.of k)) (Category.comp_id _)

/-- The rational point `a : Spec k → 𝔸¹_k` as a morphism of schemes. -/
def rationalPointHom (a : k) : Spec (.of k) ⟶ affineLine k :=
  AffineSpace.homOfVector (𝟙 (Spec (.of k))) fun _ => (Scheme.ΓSpecIso (.of k)).inv.hom a

/-- The rational point `a : Spec k → A'` of the dual line. -/
def fourierRationalPoint (a : k) : fourierBase k ⟶ fourierLine k :=
  Over.homMk (rationalPointHom k a) (AffineSpace.homOfVector_over _ _)

/-- The morphism `x ↦ (x, a)` from the line to the plane. -/
def fibreInclusionHom (a : k) : affineLine k ⟶ affinePlane k :=
  pullback.lift (𝟙 (affineLine k)) ((affineLine k ↘ Spec (.of k)) ≫ rationalPointHom k a) (by
    rw [Category.id_comp, Category.assoc, rationalPointHom, AffineSpace.homOfVector_over,
      Category.comp_id])

/-- The morphism `x ↦ (x, a)` is a morphism over `k`. -/
theorem fibreInclusionHom_over (a : k) :
    fibreInclusionHom k a ≫ (affinePlane k ↘ Spec (.of k)) = affineLine k ↘ Spec (.of k) := by
  have h : fibreInclusionHom k a ≫ affinePlane.fst k = 𝟙 _ := pullback.lift_fst _ _ _
  change fibreInclusionHom k a ≫ affinePlane.fst k ≫ (affineLine k ↘ Spec (.of k)) = _
  rw [← Category.assoc, h, Category.id_comp]

/-- The inclusion `x ↦ (x, a)` of `A` into `A × A'` as the fibre of the second projection over
the rational point `a`. -/
def fourierFibreInclusion (a : k) : fourierLine k ⟶ fourierPlane k :=
  Over.homMk (fibreInclusionHom k a) (fibreInclusionHom_over k a)

/-- The reflection `x ↦ -x` of the line, weil-conjectures' `affineLine.neg`, in `Over (Spec k)`. -/
def fourierNegation : fourierLine k ⟶ fourierLine k :=
  Over.homMk (affineLine.neg k)
    (inferInstance : (affineLine.neg k).IsOver (Spec (.of k))).comp_over

/-- The base change map `𝔸¹_{k₁} → 𝔸¹_k` of the line along a field extension `k ⊂ k₁`. -/
def fourierLineBaseChange (k₁ : Type u) [Field k₁] [Algebra k k₁] :
    (fourierLine k₁).left ⟶ (fourierLine k).left :=
  AffineSpace.map PUnit.{u + 1} (Spec.map (CommRingCat.ofHom (algebraMap k k₁)))

end Fibre

section FibreKernel

variable (k : Type u) [Field k] [Fintype k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]

/-- The kernel restricted to the fibre `A × {a}` of `pr'`: the derived pullback of
`Lψ(xx')` along `x ↦ (x, a)`, a bounded constructible complex on `A`. -/
def fourierFibreKernel (ψ : AddChar k (PadicAlgCl ℓ)) (a : k) :
    Dᵇc((fourierLine k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
    (fourierFibreInclusion k a)).obj (arithmeticFourierKernel k ℓ ψ)

/-- Compactly supported cohomology `RΓ_c(A_k̄, -)` with its arithmetic structure: the lower
shriek along `A → Spec k` for the compactification `A ⊂ D` of
`affineTraceLineCompactification`, with values bounded constructible complexes on `Spec k`. -/
def fourierLineCompactCohomology :
    Dᵇc((fourierLine k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((fourierBase k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  boundedConstructibleLowerShriekOfCompactification ℓ (f := fourierLineStructure k)
    (affineTraceLineCompactification (Spec (.of k)))

/-- The derived pullback along an arbitrary morphism of schemes, on bounded constructible
complexes: the restriction of the ambient derived pullback, which preserves bounded
constructible complexes (weil-conjectures'
`boundedConstructible_leftDerivedUpperStar_obj_of_scheme`). -/
def schemeUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Dᵇc(Y)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructible _).lift
    ((boundedConstructible _).ι ⋙
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) f).leftDerivedFunctor)
    fun K => boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ f K.obj K.property

end FibreKernel

/-- **The fibres of the arithmetic transform** (Laumon (1.2.2.1)–(1.2.2.2), pp. 141–142, and
(1.2.2.9), p. 144). For a rational point `a ∈ k` of `A'`, the restriction of `FTψ(K)` to `a` is
`RΓ_c(A_k̄, K ⊗ Lψ(ax))[1]` with its arithmetic structure, naturally in `K`, where the kernel on
the fibre is the pullback of `Lψ(xx')` along `x ↦ (x, a)`; this kernel is the Artin–Schreier
sheaf of the function `a x`, and at the origin it is the unit. -/
def ArithmeticFourierFibreStatement : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (ψ : AddChar k (PadicAlgCl ℓ)) (a : k),
    Nonempty (boundedConstructibleArithmeticFourier k ℓ ψ ⋙
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (fourierRationalPoint k a) ≅
      tensorRight (fourierFibreKernel k ℓ ψ a) ⋙ fourierLineCompactCohomology k ℓ ⋙
        shiftFunctor _ (1 : ℤ)) ∧
    Nonempty ((fourierFibreKernel k ℓ ψ a).obj ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k (affineLine k)
          (condensedFourierCharacter k ℓ ψ) (linearFunction k a))) ∧
    Nonempty (fourierFibreKernel k ℓ ψ 0 ≅ 𝟙_ _)

/-- **The transform commutes with finite extension of the constant field** (Laumon (1.2.2.9),
p. 144, the formation of the transform commutes with base change; (1.2.3.5), pp. 145–146, is the
related formula for compactly supported direct images). For a finite extension `k ⊂ k₁`,
pulling back to `𝔸¹_{k₁}` carries the transform over `k` for `ψ` to the transform over `k₁` for
the character `ψ ∘ Tr_{k₁/k}`, naturally in the input. -/
def FourierCommutesWithFiniteBaseChangeStatement : Prop :=
  ∀ (k k₁ : Type u) [Field k] [Fintype k] [Field k₁] [Fintype k₁] [Algebra k k₁] (ℓ : ℕ)
    [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)] [Fact (ringChar k₁ ≠ ℓ)]
    (ψ : AddChar k (PadicAlgCl ℓ)),
    Nonempty (boundedConstructibleArithmeticFourier k ℓ ψ ⋙
        schemeUpperStar ℓ (fourierLineBaseChange k k₁) ≅
      schemeUpperStar ℓ (fourierLineBaseChange k k₁) ⋙
        boundedConstructibleArithmeticFourier k₁ ℓ
          (ψ.compAddMonoidHom (Algebra.trace k k₁).toAddMonoidHom))

section Convolution

variable (k : Type u) [Field k]

/-- The triple product `A × A' × A''` with points `(x, x', x'')`, weil-conjectures'
`affineTripleProduct`, as an object of `Over (Spec k)`. -/
def fourierTriple : Over (Spec (.of k)) :=
  Over.mk (affineTripleProduct k ↘ Spec (.of k))

instance : LocallyOfFiniteType (fourierTriple k).hom :=
  inferInstanceAs (LocallyOfFiniteType (affineTripleProduct k ↘ Spec (.of k)))

instance : QuasiCompact (fourierTriple k).hom := by
  have : QuasiCompact (affinePlane.fst k) :=
    inferInstanceAs (QuasiCompact (pullback.fst (affineLine k ↘ Spec (.of k))
      (affineLine k ↘ Spec (.of k))))
  have : QuasiCompact (affineTripleProduct.proj₁₂ k) :=
    inferInstanceAs (QuasiCompact (pullback.fst (affinePlane.snd k) (affinePlane.fst k)))
  have : QuasiCompact (affinePlane k ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (fourierPlane k).hom)
  exact inferInstanceAs
    (QuasiCompact (affineTripleProduct.proj₁₂ k ≫ affinePlane k ↘ Spec (.of k)))

instance : IsSeparated (fourierTriple k).hom := by
  have : IsSeparated (affinePlane.fst k) :=
    inferInstanceAs (IsSeparated (pullback.fst (affineLine k ↘ Spec (.of k))
      (affineLine k ↘ Spec (.of k))))
  have : IsSeparated (affineTripleProduct.proj₁₂ k) :=
    inferInstanceAs (IsSeparated (pullback.fst (affinePlane.snd k) (affinePlane.fst k)))
  have : IsSeparated (affinePlane k ↘ Spec (.of k)) :=
    inferInstanceAs (IsSeparated (fourierPlane k).hom)
  exact inferInstanceAs
    (IsSeparated (affineTripleProduct.proj₁₂ k ≫ affinePlane k ↘ Spec (.of k)))

/-- The projection `(x, x', x'') ↦ (x, x')`. -/
def fourierTripleProj₁₂ : fourierTriple k ⟶ fourierPlane k :=
  Over.homMk (affineTripleProduct.proj₁₂ k) rfl

/-- The projection `(x, x', x'') ↦ (x', x'')` is a morphism over `k`. -/
theorem fourierTripleProj₂₃_over :
    affineTripleProduct.proj₂₃ k ≫ (affinePlane k ↘ Spec (.of k)) =
      affineTripleProduct k ↘ Spec (.of k) := by
  have h₁ : affineTripleProduct.proj₂₃ k ≫ affinePlane.fst k =
      affineTripleProduct.proj₁₂ k ≫ affinePlane.snd k := pullback.condition.symm
  have h₂ : affinePlane.snd k ≫ (affineLine k ↘ Spec (.of k)) =
      affinePlane.fst k ≫ (affineLine k ↘ Spec (.of k)) := pullback.condition.symm
  change affineTripleProduct.proj₂₃ k ≫ affinePlane.fst k ≫ (affineLine k ↘ Spec (.of k)) =
    affineTripleProduct.proj₁₂ k ≫ affinePlane.fst k ≫ (affineLine k ↘ Spec (.of k))
  rw [← Category.assoc, h₁, Category.assoc, h₂]

/-- The projection `(x, x', x'') ↦ (x', x'')`. -/
def fourierTripleProj₂₃ : fourierTriple k ⟶ fourierPlane k :=
  Over.homMk (affineTripleProduct.proj₂₃ k) (fourierTripleProj₂₃_over k)

/-- The projection `(x, x', x'') ↦ (x, x'')`. -/
def fourierTripleProj₁₃ : fourierTriple k ⟶ fourierPlane k :=
  Over.homMk (affineTripleProduct.proj₁₃ k)
    (inferInstance : (affineTripleProduct.proj₁₃ k).IsOver (Spec (.of k))).comp_over

/-- The antidiagonal `x ↦ (x, -x)` of `A × A''`, weil-conjectures' `affineLine.antidiagonal`,
a closed immersion. -/
def fourierAntidiagonal : fourierLine k ⟶ fourierPlane k :=
  Over.homMk (affineLine.antidiagonal k)
    (inferInstance : (affineLine.antidiagonal k).IsOver (Spec (.of k))).comp_over

instance : IsProper (fourierAntidiagonal k).left :=
  inferInstanceAs (IsProper (affineLine.antidiagonal k))

end Convolution

/-- **The composite kernel** (Laumon (1.2.2.1)–(1.2.2.3), pp. 141–143, and (1.2.3.1), p. 144).
For a nontrivial character `ψ`, the convolution `Rp₁₃!(p₁₂^* Lψ(xx') ⊗ p₂₃^* Lψ(x'x''))` of the
arithmetic kernel with itself on `A × A''` is the Tate-twisted, shifted unit `E(-1)[-2]` on the
antidiagonal `x'' = -x`, pushed forward to `A × A''`, as arithmetic complexes. -/
def ArithmeticFourierKernelCohomologyStatement : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (ψ : AddChar k (PadicAlgCl ℓ)), ψ ≠ 1 →
    Nonempty ((boundedConstructibleLowerShriek ℓ (fourierTripleProj₁₃ k)).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (fourierTripleProj₁₂ k)).obj (arithmeticFourierKernel k ℓ ψ) ⊗
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (fourierTripleProj₂₃ k)).obj (arithmeticFourierKernel k ℓ ψ)) ≅
      (boundedConstructibleLowerStarOfIsProper ℓ (fourierAntidiagonal k)).obj
        (boundedConstructibleTateTwist ℓ (fourierLine k) (-1) (-2)))

/-- **Inversion of the arithmetic transform** (Laumon (1.2.2.1) and Corollaire (1.2.2.3),
pp. 141–143, and (2.5.6), p. 169). For `ψ ≠ 1`, applying `FTψ` twice is naturally isomorphic,
by arithmetic maps, to pullback along `a(x) = -x` followed by the Tate twist `(-1)`.
There is a natural comparison `ρ` of this reflection-and-twist functor under Weil realization
with `weilInversionTarget k ℓ`. For each comparison `e` of the transforms and each Weil
inversion `β`, an arithmetic inversion `α` realizes to the map given by applying `e` twice,
then `β`, then the inverse of `ρ`. -/
def ArithmeticFourierInversionStatement : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (ψ : AddChar k (PadicAlgCl ℓ)), ψ ≠ 1 →
    let R := weilRealization k ℓ (fourierLine k)
    let F := boundedConstructibleArithmeticFourier k ℓ ψ
    let G := fourierTransform ψ
    let T := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (fourierNegation k) ⋙
      tensorRight (boundedConstructibleTateTwist ℓ (fourierLine k) (-1) 0)
    let T' := weilInversionTarget k ℓ
    Nonempty (F ⋙ F ≅ T) ∧
    ∃ ρ : T ⋙ R ≅ R ⋙ T',
      ∀ (e : F ⋙ R ≅ R ⋙ G) (β : G ⋙ G ≅ T'),
        ∃ α : F ⋙ F ≅ T,
          Functor.isoWhiskerRight α R ≪≫ ρ = commIsoTwice e ≪≫ Functor.isoWhiskerLeft R β

end Langlands.Henniart.Laumon
