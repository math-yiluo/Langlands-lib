import Langlands.Correspondence.Laumon.FourierRealization
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor
import WeilConjectures.WeilSheaf.FourierFirstFormula

/-!
# The Kummer lines, the Gauss line and their Fourier transforms

Laumon 1987, Remarque (1.1.3.7), p. 140, Lemme (1.4.3.1) and Proposition (1.4.3.2), pp. 149–150:
for a nontrivial Kummer character `χ`, the Kummer line `K_χ` on `𝔾_m = A ∖ {0}` is clean at the
origin of `A`, and `K_{χ⁻¹}` is clean at the origin of `A'`. The Gauss line
`G(χ, ψ) = H_c¹(𝔾_m ⊗ k̄, K_χ ⊗ Lψ)` has rank one and is the only nonzero compactly supported
cohomology. The Fourier transform satisfies `FTψ(j_! K_χ[1]) ≅ j'_! K_{χ⁻¹}[1] ⊗ G(χ, ψ)`.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [-instance] CategoryTheory.sfbRegularAbMonoidal
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.hasDerived

namespace Langlands.Henniart.Laumon

section PuncturedLine

variable (k : Type u) [Field k]

/-- The inclusion `j : 𝔾_m = A ∖ {0} ↪ A` of the basic open where the coordinate is
invertible. -/
def puncturedLineInclusion : ((affineLine k).basicOpen (lineCoordinate k)).toScheme ⟶
    affineLine k :=
  ((affineLine k).basicOpen (lineCoordinate k)).ι

instance : IsOpenImmersion (puncturedLineInclusion k) :=
  inferInstanceAs (IsOpenImmersion ((affineLine k).basicOpen (lineCoordinate k)).ι)

/-- The punctured line `𝔾_m = A ∖ {0}` as an object of `Over (Spec k)`. -/
def fourierPuncturedLine : Over (Spec (.of k)) :=
  Over.mk (puncturedLineInclusion k ≫ affineLine k ↘ Spec (.of k))

instance : LocallyOfFiniteType (fourierPuncturedLine k).hom :=
  inferInstanceAs (LocallyOfFiniteType (puncturedLineInclusion k ≫ affineLine k ↘ Spec (.of k)))

instance : QuasiCompact (puncturedLineInclusion k) :=
  inferInstanceAs (QuasiCompact ((affineLine k).basicOpen (lineCoordinate k)).ι)

instance : QuasiCompact (fourierPuncturedLine k).hom :=
  inferInstanceAs (QuasiCompact (puncturedLineInclusion k ≫ affineLine k ↘ Spec (.of k)))

instance : IsSeparated (fourierPuncturedLine k).hom :=
  inferInstanceAs (IsSeparated (puncturedLineInclusion k ≫ affineLine k ↘ Spec (.of k)))

/-- The inclusion `j : 𝔾_m ↪ A` (and `j' : 𝔾_m ↪ A'`) in `Over (Spec k)`. -/
def fourierPuncturedInclusion : fourierPuncturedLine k ⟶ fourierLine k :=
  Over.homMk (puncturedLineInclusion k) rfl

instance : IsOpenImmersion (fourierPuncturedInclusion k).left :=
  inferInstanceAs (IsOpenImmersion ((affineLine k).basicOpen (lineCoordinate k)).ι)

/-- The coordinate of `𝔾_m`, a unit. -/
def puncturedCoordinate : Γ((fourierPuncturedLine k).left, ⊤) :=
  (puncturedLineInclusion k).appTop (lineCoordinate k)

/-- The compactification `𝔾_m ⊂ A ⊂ D` of the structure morphism of `𝔾_m`. -/
def puncturedLineCompactification :
    Compactification (fourierPuncturedLine k).hom :=
  (affineTraceLineCompactification (Spec (.of k))).precomp (puncturedLineInclusion k)

/-- The origin `0 : Spec k → A`, weil-conjectures' `affineLine.zero`, in `Over (Spec k)`. -/
def fourierOrigin : fourierBase k ⟶ fourierLine k :=
  Over.homMk (affineLine.zero k) (affineLine.zero_over (k₀ := k))

instance : IsProper (fourierOrigin k).left :=
  inferInstanceAs (IsProper (affineLine.zero k))

end PuncturedLine

section Kummer

variable (k : Type u) [Field k] [Fintype k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
  (n : ℕ) {ζ₀ : k} (hζ₀ : IsPrimitiveRoot ζ₀ n)

/-- The root of unity `ζ₀` as a global function on `𝔾_m`. -/
def puncturedRootOfUnity (ζ₀ : k) : Γ((fourierPuncturedLine k).left, ⊤) :=
  (fourierPuncturedLine k).hom.appTop ((Scheme.ΓSpecIso (.of k)).inv.hom ζ₀)

omit [Fintype k] in
include hζ₀ in
/-- `ζ₀ⁿ = 1` on `𝔾_m`. -/
theorem puncturedRootOfUnity_pow : puncturedRootOfUnity k ζ₀ ^ n = 1 := by
  rw [puncturedRootOfUnity, ← map_pow, ← map_pow, hζ₀.pow_eq_one, map_one, map_one]

/-- The scheme of `n`-th roots `t` of the coordinate `x` of `𝔾_m`, with its projection `t ↦ tⁿ`
to `𝔾_m` (weil-conjectures' `Scheme.kummerCover` of the coordinate): the Kummer covering of order
`n`. For `n > 0` invertible in `k` and a primitive `n`-th root of unity in `k` it is a
`μ_n(k)`-torsor over `𝔾_m`, `ζ` acting by `t ↦ ζ t` (`Scheme.EtaleTorsor.kummer`). -/
abbrev kummerCovering [NeZero n] : Scheme.{u} :=
  (fourierPuncturedLine k).left.kummerCover n (puncturedCoordinate k)

/-- The pushforward of the regular coefficient module along the Kummer covering. -/
def kummerPushforward [NeZero n] :=
  (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
    ((fourierPuncturedLine k).left.kummerCoverπ n (puncturedCoordinate k))).obj
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (kummerCovering k n)))

/-- The action on `kummerPushforward` of the deck transformation `t ↦ ζ₀ᵐ t`, by pullback of
sections. -/
def kummerDeckAction [NeZero n] (m : ℕ) : End (kummerPushforward k ℓ n) :=
  End.of <| (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
    ((fourierPuncturedLine k).left.kummerCoverπ n (puncturedCoordinate k))).map
      (((CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
        (Scheme.kummerVadd (puncturedRootOfUnity k ζ₀) (puncturedRootOfUnity_pow k n hζ₀)
          m)).homEquiv _ _)
          (Functor.Monoidal.εIso (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
            (Scheme.kummerVadd (puncturedRootOfUnity k ζ₀) (puncturedRootOfUnity_pow k n hζ₀)
              m))).inv) ≫
    (CondensedRing.lowerStarComp (Profinite.padicAlgClRingObj ℓ)
      (Scheme.kummerVadd (puncturedRootOfUnity k ζ₀) (puncturedRootOfUnity_pow k n hζ₀) m)
      ((fourierPuncturedLine k).left.kummerCoverπ n (puncturedCoordinate k))).hom.app _ ≫
    eqToHom (congrArg (fun t ↦ (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) t).obj
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (kummerCovering k n))))
        (Scheme.kummerVadd_comp_π _ _ m))

/-- The character projector `e_χ = n⁻¹ ∑_{m ∈ ℤ/n} χ(m)⁻¹ σ_m` on `kummerPushforward`, where
`σ_m` is the action of `t ↦ ζ₀ᵐ t` (the analogue of weil-conjectures'
`condensedArtinSchreierProjector`). -/
def kummerProjector [NeZero n] (χ : AddChar (ZMod n) (PadicAlgCl ℓ)) :
    End (kummerPushforward k ℓ n) :=
  ∑ m : Fin n, End.of ((kummerDeckAction k ℓ n hζ₀ m).asHom ≫
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
      ((fourierPuncturedLine k).left.kummerCoverπ n (puncturedCoordinate k))).map
        (Mod.regularEndRingHom
          (MonObj.Γ.mapFunctorMonoidHom (upperStarFromPoint (kummerCovering k n))
            (Profinite.PadicAlgCl.constRingHom.{u} ℓ
              ((n : PadicAlgCl ℓ)⁻¹ * χ (-(m : ZMod n)))))).asHom)

/-- **The Kummer line** `K_χ` on `𝔾_m` (Laumon, Remarque (1.1.3.7)): the image of the character
projector `kummerProjector` on the pushforward of the coefficients along the Kummer covering
of order `n`, for a character `χ` of `μ_n(k) = ⟨ζ₀⟩ ≅ ℤ/n`. -/
def kummerLine [NeZero n] (χ : AddChar (ZMod n) (PadicAlgCl ℓ)) :=
  image (kummerProjector k ℓ n hζ₀ χ).asHom

/-- The arithmetic Artin–Schreier line `Lψ(x)` restricted to `𝔾_m`. -/
def puncturedArtinSchreierLine (ψ : AddChar k (PadicAlgCl ℓ)) :=
  condensedArtinSchreierSheafOf (Profinite.padicAlgClRingObj ℓ) k (fourierPuncturedLine k).left
    (condensedFourierCharacter k ℓ ψ) (puncturedCoordinate k)

/-- **The Gauss line** `G(χ, ψ)` (Laumon (1.4.3.2)): the arithmetic complex
`RΓ_c(𝔾_m ⊗ k̄, K_χ ⊗ Lψ)[1]` on `Spec k`, computed with the compactification `𝔾_m ⊂ A ⊂ D`; its
degree `0` cohomology is `H_c¹(𝔾_m ⊗ k̄, K_χ ⊗ Lψ)` with its geometric Frobenius. -/
def gaussLine [NeZero n] (χ : AddChar (ZMod n) (PadicAlgCl ℓ)) (ψ : AddChar k (PadicAlgCl ℓ)) :=
  (shiftFunctor _ (1 : ℤ)).obj
    ((rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ)
      (puncturedLineCompactification k)).obj
      ((tensorRight ((DerivedCategory.singleFunctor _ 0).obj
        (puncturedArtinSchreierLine k ℓ ψ))).obj
        ((DerivedCategory.singleFunctor _ 0).obj (kummerLine k ℓ n hζ₀ χ))))

end Kummer

/-- **Kummer lines, the Gauss line and their Fourier transform** (Laumon, Remarque (1.1.3.7),
p. 140, Lemme (1.4.3.1) and Proposition (1.4.3.2), pp. 149–150, and SGA 4½ *Sommes trig.*
(4.3) and (4.20)). Let `n > 0`, let `k` be a finite field containing a primitive `n`-th root of
unity `ζ₀` and let `ψ` be a nontrivial additive character. For a nontrivial character `χ` of
`μ_n(k) = ⟨ζ₀⟩ ≅ ℤ/n`,
the Kummer lines `K_χ` and `K_{χ⁻¹}` on `𝔾_m` are bounded constructible complexes in degree `0`;
`K_χ` is clean at the origin, `Rj_* K_χ ≅ j_! K_χ` on `A`; the pullback of the Gauss line
`RΓ_c(𝔾_m ⊗ k̄, K_χ ⊗ Lψ)[1]` to `Spec k̄` is the free module of rank one in degree `0`, so that
`H_c^i(𝔾_m ⊗ k̄, K_χ ⊗ Lψ)` vanishes for `i ≠ 1` and has rank one for `i = 1`; and
`FTψ(j_! K_χ[1]) ≅ j'_! K_{χ⁻¹}[1] ⊗ G(χ, ψ)`, with `G(χ, ψ)` pulled back to `A'`. For the
trivial character the constant and punctual formulas hold: `FTψ(δ₀) ≅ E_{A'}[1]` and
`FTψ(E_A) ≅ δ_{0'}(-1)[-1]`. -/
def KummerGaussFourierStatement : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]
    (n : ℕ) [NeZero n] (ζ₀ : k) (hζ₀ : IsPrimitiveRoot ζ₀ n)
    (χ : AddChar (ZMod n) (PadicAlgCl ℓ)) (ψ : AddChar k (PadicAlgCl ℓ)), ψ ≠ 1 →
    (χ ≠ 1 →
      boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (fourierPuncturedLine k).left)
        ((DerivedCategory.singleFunctor _ 0).obj (kummerLine k ℓ n hζ₀ χ)) ∧
      boundedConstructible
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (fourierPuncturedLine k).left)
        ((DerivedCategory.singleFunctor _ 0).obj (kummerLine k ℓ n hζ₀ χ⁻¹)) ∧
      Nonempty ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
          (puncturedLineInclusion k)).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj (kummerLine k ℓ n hζ₀ χ)) ≅
        (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ)
          (Compactification.ofIsOpenImmersion (puncturedLineInclusion k))).obj
          ((DerivedCategory.singleFunctor _ 0).obj (kummerLine k ℓ n hζ₀ χ))) ∧
      Nonempty ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))).leftDerivedFunctor.obj
          (gaussLine k ℓ n hζ₀ χ ψ) ≅
        (DerivedCategory.singleFunctor _ 0).obj (Mod.regular
          (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of (AlgebraicClosure k)))))) ∧
      Nonempty ((ambientArithmeticFourier k ℓ ψ).obj ((shiftFunctor _ (1 : ℤ)).obj
          ((rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ)
            (Compactification.ofIsOpenImmersion (puncturedLineInclusion k))).obj
            ((DerivedCategory.singleFunctor _ 0).obj (kummerLine k ℓ n hζ₀ χ)))) ≅
        (tensorRight ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ)
            (affineLine k ↘ Spec (.of k))).leftDerivedFunctor.obj (gaussLine k ℓ n hζ₀ χ ψ))).obj
          ((shiftFunctor _ (1 : ℤ)).obj
            ((rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ℓ)
              (Compactification.ofIsOpenImmersion (puncturedLineInclusion k))).obj
              ((DerivedCategory.singleFunctor _ 0).obj (kummerLine k ℓ n hζ₀ χ⁻¹)))))) ∧
    Nonempty ((boundedConstructibleArithmeticFourier k ℓ ψ).obj
        ((boundedConstructibleLowerStarOfIsProper ℓ (fourierOrigin k)).obj (𝟙_ _)) ≅
      (shiftFunctor _ (1 : ℤ)).obj (𝟙_ _)) ∧
    Nonempty ((boundedConstructibleArithmeticFourier k ℓ ψ).obj (𝟙_ _) ≅
      (boundedConstructibleLowerStarOfIsProper ℓ (fourierOrigin k)).obj
        (boundedConstructibleTateTwist ℓ (fourierBase k) (-1) (-1)))

end Langlands.Henniart.Laumon
