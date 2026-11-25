/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Projective space over a base scheme

`ℙ(n; S)` is the projective `n`-space over an arbitrary base scheme `S`, defined as the base
change `S ×_{Spec ℤ} ℙⁿ_ℤ` of the integral model `ℙⁿ_ℤ = Proj ℤ[T]` along the structure
morphism of `S`, exactly as Mathlib's affine space `𝔸(n; S)` is defined as `S ×_{Spec ℤ} 𝔸ⁿ_ℤ`.
Here `n : Type u` is the index type of the *homogeneous* coordinates, so that the space Stacks
writes `ℙⁿ_S` is `ℙ(Fin (n + 1); S)`.

Mathlib has no relative projective space to reuse, only the absolute `Proj` of a graded ring,
so everything below is new; the integral model itself is
`Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)`.

Morphisms *into* `ℙ(n; S)` are constructed from families of global sections generating the
unit ideal in `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections`, and the standard
affine charts `standardOpen n S i ≅ 𝔸({j : n // j ≠ i}; S)` are in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts`.

## Main definitions

- `AlgebraicGeometry.Proj.projectiveSpaceOverAffine` — the projective space `ℙ^σ_A` over an
  affine base, i.e. `Proj` of the polynomial ring `A[T]` with its total-degree grading.
- `AlgebraicGeometry.Proj.projectiveSpaceOverAffineToSpec` — its structure morphism
  `ℙ^σ_A ⟶ Spec A`.
- `AlgebraicGeometry.ProjectiveSpace` — `ℙ(n; S)` is the projective `n`-space over `S`, with
  structure morphism `ℙ(n; S) ↘ S`.
- `AlgebraicGeometry.ProjectiveSpace.map` — functoriality of `ℙ(n; S)` in the base `S`.
- `AlgebraicGeometry.ProjectiveSpace.liftBaseChange` — the morphism `T ⟶ ℙ(n; X)` induced by a
  morphism `T ⟶ X` and a morphism `T ⟶ ℙ(n; S)` agreeing over `S`.
- `AlgebraicGeometry.ProjectiveLine` — the projective line `ℙ¹_S = ℙ(ULift (Fin 2); S)`.

## Main results

- `AlgebraicGeometry.ProjectiveSpace.instIsProper` — for a finite index type, the structure
  morphism `ℙ(n; S) ↘ S` is proper.
- `AlgebraicGeometry.ProjectiveSpace.instIsEmpty` — `ℙ(n; S)` is empty if `n` is.
- `AlgebraicGeometry.ProjectiveSpace.isPullback_map` — projective space commutes with base
  change: for `g : X ⟶ S`, the scheme `ℙ(n; X)` is the base change of `ℙ(n; S)` along `g`.

## Implementation notes

Mathlib does not make the total-degree grading of `MvPolynomial σ A` a global instance, since
one may want to grade by another weight function; it is enabled here as a local instance. To
keep it out of the statements of the results below, `Proj.projectiveSpaceOverAffine σ A` is a plain
definition rather than an abbreviation, so that downstream files need not re-enable the
instance.

Defining `ℙ(n; S)` by base change is the cheap route: it needs no gluing, and properness of
`ℙ(n; S) ↘ S` follows from properness of the integral model by base change. The blueprint's
`def:nagata-relative-projective-space` instead constructs `ℙ^r_X` as the relative `Proj` of
a symmetric algebra, and requires its standard opens to be the relative spectra of the
degree-zero homogeneous localizations. The definition here is intended to be canonical for
everything that only needs `ℙ(n; S)` as a scheme over `S`; the chart interface is what
relative `Proj` would add on top, and the comparison of the two is left to the file that
builds relative `Proj`.

## TODO

- `ℙ(n; Spec A) ≅ Proj.projectiveSpaceOverAffine n A` over `Spec A`, the analogue of
  `AlgebraicGeometry.AffineSpace.SpecIso`. This needs `Proj` to commute with base change,
  which Mathlib does not have, so `Proj.projectiveSpaceOverAffine` and `ProjectiveSpace` are
  for now two unrelated definitions.

## Blueprint

`ProjectiveSpace` implements `def:nagata-projective-space-base-change` of the Nagata
compactification blueprint, which is the base-change substitute for
`def:nagata-relative-projective-space` described above, `ProjectiveSpace.instIsProper`
implements `lemma:nagata-projective-space-base-change-proper` and
`ProjectiveSpace.isPullback_map` implements
`lemma:nagata-projective-space-base-change-pullback`. `Proj.projectiveSpaceOverAffine` is
`def:nagata-affine-proj` for a polynomial ring.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

section Affine

attribute [local instance] MvPolynomial.gradedAlgebra

variable (σ : Type u) (A : Type u) [CommRing A]

/-- The projective space `ℙ^σ_A` over an affine base, defined as `Proj` of the polynomial
ring `A[T]` in the variables `σ` with its total-degree grading.
(blueprint: `def:nagata-affine-proj`, for a polynomial ring) -/
def Proj.projectiveSpaceOverAffine : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule σ A)

/-- The structure morphism `ℙ^σ_A ⟶ Spec A` of the projective space over an affine base. -/
def Proj.projectiveSpaceOverAffineToSpec : Proj.projectiveSpaceOverAffine σ A ⟶ Spec (.of A) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule σ A) ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.homogeneousSubmoduleZeroEquiv σ A).toRingHom)

/-- **Projective space over an affine base is proper**: for a finite index type `σ`, the
structure morphism `ℙ^σ_A ⟶ Spec A` is proper. -/
instance Proj.instIsProperProjectiveSpaceOverAffineToSpec [Finite σ] :
    IsProper (Proj.projectiveSpaceOverAffineToSpec σ A) := by
  rw [Proj.projectiveSpaceOverAffineToSpec]
  infer_instance

end Affine

/-- `ℙ(n; S)` is the projective `n`-space over `S`, that is, the base change
`S ×_{Spec ℤ} ℙⁿ_ℤ` of the integral model along the structure morphism of `S`.
Note that `n : Type u` indexes the *homogeneous* coordinates, so that the classical `ℙⁿ_S` is
`ℙ(Fin (n + 1); S)`.
(blueprint: `def:nagata-projective-space-base-change`) -/
def ProjectiveSpace (n : Type u) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)))

namespace ProjectiveSpace

/-- `ℙ(n; S)` is the projective `n`-space over `S`. -/
scoped[AlgebraicGeometry] notation "ℙ(" n "; " S ")" => ProjectiveSpace n S

variable (n : Type u) (S : Scheme.{u})

@[simps -isSimp]
instance over : ℙ(n; S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The map from the projective `n`-space over `S` to the integral model `ℙⁿ_ℤ`. -/
def toProjInt : ℙ(n; S) ⟶ Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ) := pullback.snd _ _

/-- A morphism into `ℙ(n; S)` is determined by its composites with the structure morphism to
`S` and with the map to the integral model `ℙⁿ_ℤ`. -/
@[ext 1100]
lemma hom_ext {X : Scheme.{u}} {f g : X ⟶ ℙ(n; S)}
    (h₁ : f ≫ ℙ(n; S) ↘ S = g ≫ ℙ(n; S) ↘ S)
    (h₂ : f ≫ toProjInt n S = g ≫ toProjInt n S) : f = g :=
  pullback.hom_ext h₁ h₂

/-- The defining pullback square of `ℙ(n; S)`: it is the base change of the integral model
`ℙⁿ_ℤ` along the structure morphism of `S`. -/
lemma isPullback_over_toProjInt :
    IsPullback (ℙ(n; S) ↘ S) (toProjInt n S) (terminal.from S)
      (terminal.from (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ))) :=
  IsPullback.of_hasPullback _ _

/-- **`ℙ(n; S)` is proper over `S`**: for a finite index type `n`, the structure morphism
`ℙ(n; S) ↘ S` is proper, being a base change of the proper morphism `ℙⁿ_ℤ ⟶ Spec ℤ`.

Together with the instances for closed immersions and composites, `inferInstance` shows that
`i ≫ ℙ(n; S) ↘ S` is proper for any closed immersion `i : X ⟶ ℙ(n; S)`: projective morphisms
are proper (blueprint: `lem-pc-projective-proper`). -/
instance instIsProper [Finite n] : IsProper (ℙ(n; S) ↘ S) := by
  have hZ : terminal.from (Spec (.of (ULift.{u} ℤ))) =
      (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).hom := terminal.hom_ext _ _
  have hP : terminal.from (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)) =
      Proj.projectiveSpaceOverAffineToSpec n (ULift.{u} ℤ) ≫ terminal.from _ := terminal.hom_ext _ _
  have : IsIso (terminal.from (Spec (.of (ULift.{u} ℤ)))) := hZ ▸ inferInstance
  have : IsProper (terminal.from (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ))) :=
    hP ▸ inferInstance
  exact inferInstanceAs (IsProper (pullback.fst _ _))

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **Projective space without homogeneous coordinates is empty**: if `n` is empty, the standard
opens `D₊(Tᵢ)`, which cover `ℙⁿ_ℤ`, form an empty family. -/
instance instIsEmpty [IsEmpty n] : IsEmpty ℙ(n; S) := by
  have h := Proj.iSup_basicOpen_eq_top' (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ))
    MvPolynomial.X (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X _ i⟩)
    (MvPolynomial.adjoin_range_X_eq_top n _)
  rw [iSup_of_empty] at h
  refine ⟨fun x ↦ ?_⟩
  have : (toProjInt n S).base x ∈ (⊤ : (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)).Opens) :=
    trivial
  rw [← h] at this
  exact this

/-- `ℙ(n; S)` is functorial in the base `S`: `map n f` is the unique morphism making

```
            map n f
  ℙ(n; S) ----------> ℙ(n; T)
     |                   |
     | ↘                 | ↘
     ↓                   ↓
     S ------- f ------> T
```

commute and compatible with the maps to the integral model, i.e. making

```
            map n f
  ℙ(n; S) ----------> ℙ(n; T)
        ╲             ╱
    toProjInt     toProjInt
          ╲       ╱
           ↘ ℙⁿ_ℤ ↙
```

commute as well. -/
def map {S T : Scheme.{u}} (f : S ⟶ T) : ℙ(n; S) ⟶ ℙ(n; T) :=
  pullback.lift (ℙ(n; S) ↘ S ≫ f) (toProjInt n S) (terminal.hom_ext _ _)

/-- `map n f` is a morphism over `f`:

```
            map n f
  ℙ(n; S) ----------> ℙ(n; T)
     |                   |
     | ↘                 | ↘
     ↓                   ↓
     S ------- f ------> T
```

commutes. -/
@[reassoc (attr := simp)]
lemma map_over {S T : Scheme.{u}} (f : S ⟶ T) :
    map n f ≫ ℙ(n; T) ↘ T = ℙ(n; S) ↘ S ≫ f :=
  pullback.lift_fst _ _ _

/-- `map n f` is compatible with the maps to the integral model `ℙⁿ_ℤ`:

```
            map n f
  ℙ(n; S) ----------> ℙ(n; T)
        ╲             ╱
    toProjInt     toProjInt
          ╲       ╱
           ↘ ℙⁿ_ℤ ↙
```

commutes. -/
@[reassoc (attr := simp)]
lemma map_toProjInt {S T : Scheme.{u}} (f : S ⟶ T) :
    map n f ≫ toProjInt n T = toProjInt n S :=
  pullback.lift_snd _ _ _

@[simp]
lemma map_id : map n (𝟙 S) = 𝟙 ℙ(n; S) := by
  ext1 <;> simp

@[reassoc, simp]
lemma map_comp {S S' S'' : Scheme.{u}} (f : S ⟶ S') (g : S' ⟶ S'') :
    map n (f ≫ g) = map n f ≫ map n g := by
  ext1 <;> simp

/-- **Projective space commutes with base change**: for a morphism `g : X ⟶ S`, the square

```
            map n g
  ℙ(n; X) ----------> ℙ(n; S)
     |                   |
     | ↘                 | ↘
     ↓                   ↓
     X ------- g ------> S
```

is cartesian, i.e. `ℙ(n; X)` is the base change of `ℙ(n; S)` along `g`. Indeed, both squares in

```
            map n g          toProjInt n S
  ℙ(n; X) ----------> ℙ(n; S) -------------> ℙⁿ_ℤ
     |                   |                     |
     | ↘                 | ↘                   |
     ↓                   ↓                     ↓
     X ------- g ------> S --------------> Spec ℤ
```

are cartesian, and so is the outer rectangle.
(blueprint: `lemma-nagata-projective-space-base-change-pullback`) -/
lemma isPullback_map {X S : Scheme.{u}} (g : X ⟶ S) :
    IsPullback (map n g) (ℙ(n; X) ↘ X) (ℙ(n; S) ↘ S) g := by
  refine (IsPullback.paste_horiz_iff (isPullback_over_toProjInt n S).flip (map_over n g)).mp ?_
  rw [map_toProjInt, terminal.comp_from]
  exact (isPullback_over_toProjInt n X).flip

/-- If `g : X ⟶ S` is proper, so is `map n g : ℙ(n; X) ⟶ ℙ(n; S)`, being the base change of
`g` along the structure morphism `ℙ(n; S) ↘ S`. -/
instance isProper_map {X S : Scheme.{u}} (g : X ⟶ S) [IsProper g] : IsProper (map n g) :=
  MorphismProperty.of_isPullback (isPullback_map n g).flip inferInstance

section LiftBaseChange

variable {n} {X S T : Scheme.{u}} {g : X ⟶ S} (a : T ⟶ X) (b : T ⟶ ℙ(n; S))
  (w : a ≫ g = b ≫ ℙ(n; S) ↘ S)

/-- A morphism `a : T ⟶ X` and a morphism `b : T ⟶ ℙ(n; S)` agreeing over `S` induce a morphism
`liftBaseChange a b w : T ⟶ ℙ(n; X)`, the unique one making

```
        T
        |  ╲
        |    ╲  b
   lift |      ╲
        ↓        ↘
     ℙ(n; X) --- map n g ---> ℙ(n; S)
        |                        |
        | ↘                      | ↘
        ↓                        ↓
        X --------- g ---------> S
```

commute, the vertical arrow marked `lift` on the left; its composite with `ℙ(n; X) ↘ X` is `a`.
This is the universal property of `ℙ(n; X)` as the base change of `ℙ(n; S)` along `g`, see
`AlgebraicGeometry.ProjectiveSpace.isPullback_map`. -/
def liftBaseChange : T ⟶ ℙ(n; X) :=
  (isPullback_map n g).lift b a w.symm

/-- `liftBaseChange a b w` is a morphism over `a`:

```
  T --- liftBaseChange a b w ---> ℙ(n; X)
      ╲                              |
        ╲  a                         | ↘
          ↘                          ↓
                                     X
```

commutes. -/
@[reassoc (attr := simp)]
lemma liftBaseChange_over : liftBaseChange a b w ≫ ℙ(n; X) ↘ X = a :=
  (isPullback_map n g).lift_snd _ _ _

/-- `liftBaseChange a b w` recovers `b` after composing with `map n g`:

```
  T --- liftBaseChange a b w ---> ℙ(n; X)
      ╲                              |
        ╲  b                         | map n g
          ↘                          ↓
                                  ℙ(n; S)
```

commutes. -/
@[reassoc (attr := simp)]
lemma liftBaseChange_map : liftBaseChange a b w ≫ map n g = b :=
  (isPullback_map n g).lift_fst _ _ _

/-- `liftBaseChange a b w` is compatible with the maps to the integral model `ℙⁿ_ℤ`:

```
  T --- liftBaseChange a b w ---> ℙ(n; X)
      ╲                              |
        ╲  b                         | toProjInt n X
          ↘                          ↓
        ℙ(n; S) --- toProjInt n S --> ℙⁿ_ℤ
```

commutes. -/
@[reassoc (attr := simp)]
lemma liftBaseChange_toProjInt :
    liftBaseChange a b w ≫ toProjInt n X = b ≫ toProjInt n S := by
  rw [← map_toProjInt n g, liftBaseChange_map_assoc]

/-- If `g : X ⟶ S` is separated, so is `map n g : ℙ(n; X) ⟶ ℙ(n; S)`, being the base change
of `g` along the structure morphism `ℙ(n; S) ↘ S`. -/
instance isSeparated_map [IsSeparated g] : IsSeparated (map n g) :=
  MorphismProperty.of_isPullback (isPullback_map n g).flip inferInstance

/-- The lift of an immersion `b : T ⟶ ℙ(n; S)` is an immersion, since `liftBaseChange a b w ≫
map n g = b`. -/
instance isImmersion_liftBaseChange [IsImmersion b] : IsImmersion (liftBaseChange a b w) :=
  have : IsImmersion (liftBaseChange a b w ≫ map n g) := by
    rw [liftBaseChange_map]
    infer_instance
  .of_comp _ (map n g)

/-- The lift of a closed immersion `b : T ⟶ ℙ(n; S)` along a separated morphism `g` is a
closed immersion: `map n g` is separated, being a base change of `g`, and closed immersions
cancel along separated morphisms.
(blueprint: `theorem-chow-s-lemma-projective-form--2`, general statement) -/
instance isClosedImmersion_liftBaseChange [IsSeparated g] [IsClosedImmersion b] :
    IsClosedImmersion (liftBaseChange a b w) :=
  have : IsClosedImmersion (liftBaseChange a b w ≫ map n g) := by
    rw [liftBaseChange_map]
    infer_instance
  .of_comp _ (map n g)

/-- The lift of `q ≫ e` along a cartesian square is the base change of `e`: if

```
       q
   T -----> T₀
   |        |
 a |        | e ≫ ℙ(n; S) ↘ S
   ↓        ↓
   X -----> S
       g
```

is cartesian and `e : T₀ ⟶ ℙ(n; S)`, then `liftBaseChange a (q ≫ e) w : T ⟶ ℙ(n; X)` is the
base change of `e` along `map n g`. In particular it is an immersion (resp. a closed immersion)
if `e` is, with no hypothesis on `g`. -/
lemma isPullback_liftBaseChange {T₀ : Scheme.{u}} {q : T ⟶ T₀} {e : T₀ ⟶ ℙ(n; S)}
    (h : IsPullback q a (e ≫ ℙ(n; S) ↘ S) g) (w : a ≫ g = (q ≫ e) ≫ ℙ(n; S) ↘ S) :
    IsPullback q (liftBaseChange a (q ≫ e) w) e (map n g) :=
  h.of_bot' (isPullback_map n g)

end LiftBaseChange

end ProjectiveSpace

/-- The **projective line** `ℙ¹_S` over a scheme `S`, with structure morphism
`ProjectiveLine S ↘ S`. Following `AlgebraicGeometry.ProjectiveSpace`, whose index type is
that of the *homogeneous* coordinates, this is `ℙ(ULift (Fin 2); S)`. It is an abbreviation,
so that the instances of `ℙ(n; S)` — the `CanonicallyOver` structure and properness among
them — apply to it unchanged. -/
abbrev ProjectiveLine (S : Scheme.{u}) : Scheme.{u} := ℙ(ULift.{u} (Fin 2); S)

end AlgebraicGeometry
