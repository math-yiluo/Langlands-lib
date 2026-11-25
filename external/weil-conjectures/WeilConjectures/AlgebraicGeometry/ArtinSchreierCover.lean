/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.Etale.StandardEtale
import WeilConjectures.AlgebraicGeometry.ArtinSchreier
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover.Properties

/-! # Artin–Schreier covers of global functions

Source: blueprint, Fourier–Deligne transform, lemma-artin-schreier-character-sheaf,
lemma-artin-schreier-character-sheaf; Stacks Project, Tag 0A3J (blueprint:
lemma-artin-schreier-character-sheaf).

The cover is constructed by base change from the polynomial quotient over the global
functions. Its affine presentations identify it with the relative spectrum in the source.
The empty scheme is included: the characteristic hypothesis says only that `p * 1 = 0`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial

noncomputable section

namespace AlgebraicGeometry

/-- The equation defining the Artin–Schreier cover.
Source: blueprint, lemma-artin-schreier-character-sheaf, first sentence (blueprint:
lemma-artin-schreier-character-sheaf). -/
def artinSchreierCoverPolynomial (p : ℕ) (X : Scheme.{u}) (f : Γ(X, ⊤)) :
    Polynomial Γ(X, ⊤) :=
  Polynomial.X ^ p - Polynomial.X - Polynomial.C f

/-- The Artin–Schreier cover of `f`, as a scheme over `X`. This is the base change along
`X.toSpecΓ` of the spectrum of the actual quotient ring `Γ(X)[T]/(T^p-T-f)`.
Source: blueprint, lemma-artin-schreier-character-sheaf, first sentence (blueprint:
lemma-artin-schreier-character-sheaf). -/
def artinSchreierCover (p : ℕ) (X : Scheme.{u}) (f : Γ(X, ⊤)) : Over X :=
  Over.mk (pullback.fst X.toSpecΓ
    (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (AdjoinRoot (artinSchreierCoverPolynomial p X f))))))

/-- The class of `T` on the Artin–Schreier cover, pulled back from its quotient-ring model.
Source: blueprint, lemma-artin-schreier-character-sheaf, the coordinate `T` (blueprint:
lemma-artin-schreier-character-sheaf). -/
def artinSchreierCoverCoordinate (p : ℕ) (X : Scheme.{u}) (f : Γ(X, ⊤)) :
    Γ((artinSchreierCover p X f).left, ⊤) :=
  (pullback.snd X.toSpecΓ
    (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (AdjoinRoot (artinSchreierCoverPolynomial p X f)))))).appTop
    ((Scheme.ΓSpecIso (.of (AdjoinRoot (artinSchreierCoverPolynomial p X f)))).inv
      (AdjoinRoot.root (artinSchreierCoverPolynomial p X f)))

/-- All properties of the Artin–Schreier covering, including its translation action and
canonical equivariant automorphism group. The source of the centralizer is the group of
locally constant functions, canonically the global sections of the constant étale sheaf.
The normalization on every open where such a function is constant specifies the canonical
isomorphism, including on disconnected bases. The sheaf torsor is identified with the
represented presheaf, and the action of each constant section is identified with the
specified translation.
Source: blueprint, lemma-artin-schreier-character-sheaf (blueprint:
lemma-artin-schreier-character-sheaf).

Proof: (1) The affine quotient has monic basis `1,T,...,T^(p-1)` by
lem-weil-pbc-monic-quotient-free. Its derivative is `-1`, so
lem-weil-pbc-standard-etale-monic-derivative gives étaleness and degree `p`.
(2) Maps into the cover are roots, by lem-weil-pbc-morphism-into-affine-scheme,
lem-asd-polynomial-quotient-hom-equivalence and lem-weil-pbc-scheme-morphism-gluing.
(3) Translation preserves the equation since `a^p=a`, by
lem-sc-field-artin-schreier-kernel; its inverse subtracts `a`.
(4) Over an algebraically closed field every root is uniquely `r+a`, by
proposition-p-torsion-smooth-proper-curve--2. This proves simple transitivity and surjectivity.
(5) Representability is a sheaf by lem-weil-pbc-small-etale-representable-presheaf-sheaf.
Differences of roots are locally constant by lem-fd-frobenius-fixed-sections and
lem-weil-pbc-constant-sheaf-sections-locally-constant. The cover trivializes this sheaf;
situation-conventions supplies covers after pullback.
(6) For an automorphism `g`, the difference `g*T-T` is a Frobenius-fixed function on `Y`.
It commutes with all translations exactly when that function is invariant.
(7) Invariant functions descend uniquely to the base: geometric transitivity gives
constancy on fibres, and lem-weil-pbc-etale-morphism-open-map makes the descended function
locally constant. Conversely, glue translations on its clopen fibres. Addition corresponds
to composition. This gives the normalized centralizer isomorphism.
(8) A geometric fibre proves faithfulness when the base is nonempty. On connected `Y`
the difference function is constant, so all automorphisms are translations. Over an empty
base the cover is empty and its automorphism group has one element. -/
theorem artinSchreier_cover_properties (p : ℕ) [Fact p.Prime]
    (X : Scheme.{u}) (hchar : (p : Γ(X, ⊤)) = 0) (f : Γ(X, ⊤)) :
    IsFinite (artinSchreierCover p X f).hom ∧
    Etale (artinSchreierCover p X f).hom ∧
    (artinSchreierCover p X f).hom.IsFiniteLocallyFreeOfDegree p ∧
    ∃ σ : Multiplicative (ZMod p) →* Aut (artinSchreierCover p X f),
      (∀ a : ZMod p, (σ (Multiplicative.ofAdd a)).asIso.hom.left.appTop
          (artinSchreierCoverCoordinate p X f) =
        artinSchreierCoverCoordinate p X f + (a.val : Γ((artinSchreierCover p X f).left, ⊤))) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Nonempty {s : Spec (.of Ω) ⟶ (artinSchreierCover p X f).left //
          s ≫ (artinSchreierCover p X f).hom = x} ∧
        ∀ s t : {s : Spec (.of Ω) ⟶ (artinSchreierCover p X f).left //
          s ≫ (artinSchreierCover p X f).hom = x},
          ∃! a : ZMod p, t.val = s.val ≫ (σ (Multiplicative.ofAdd a)).asIso.hom.left) ∧
      (∃ (R : Sheaf.Torsor
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))))
          (e : R.sheaf.obj ≅ (Scheme.Etale.forget X).op ⋙
            yoneda.obj (artinSchreierCover p X f) ⋙ uliftFunctor.{u + 1}),
        ∀ (U : X.Etale) (a : ZMod p) (s : R.sheaf.obj.obj (Opposite.op U)),
          (e.hom.app (Opposite.op U)
            (R.vadd (Opposite.op U)
              (((toSheafify X.smallEtaleTopology
                ((Functor.const X.Etaleᵒᵖ).obj
                  (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app
                    (Opposite.op U)) (ULift.up a)) s)).down =
            (e.hom.app (Opposite.op U) s).down ≫ (σ (Multiplicative.ofAdd a)).asIso.hom) ∧
      (Nonempty X → Function.Injective σ) ∧
      (∃ E : Multiplicative (LocallyConstant X (ZMod p)) ≃*
          Subgroup.centralizer (Set.range σ),
        ∀ (b : LocallyConstant X (ZMod p)) (a : ZMod p) (U : X.Opens),
          (∀ x : U, b x = a) →
          ((artinSchreierCover p X f).hom ⁻¹ᵁ U).ι ≫
              (E (Multiplicative.ofAdd b)).val.asIso.hom.left =
            ((artinSchreierCover p X f).hom ⁻¹ᵁ U).ι ≫
              (σ (Multiplicative.ofAdd a)).asIso.hom.left) ∧
      (ConnectedSpace (artinSchreierCover p X f).left → Function.Bijective σ) ∧
      (IsEmpty X → IsEmpty (artinSchreierCover p X f).left ∧
        Subsingleton (Aut (artinSchreierCover p X f))) :=
  adjoinRootCover_artinSchreier_properties (P := artinSchreierCoverPolynomial p X f) rfl hchar

end AlgebraicGeometry
