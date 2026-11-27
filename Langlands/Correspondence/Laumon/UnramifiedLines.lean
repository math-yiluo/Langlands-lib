import Langlands.Correspondence.Laumon.FieldMonodromy
import Langlands.Correspondence.Laumon.Completion
import Langlands.Galois.FiniteField.Frobenius

/-!
# Unramified lines and restriction to the local Weil group

A character of the Library's `ladicUnramifiedCharacters` of `LaurentSeries k` is trivial on
inertia, so it factors through the residue Galois group of the finite field `k`. This module
attaches to it an arithmetic lisse line on `Spec k`, states that its pullbacks to the end traits
have the character as monodromy through the completion bridge, and that its Frobenius is the
character's value on a Weil Frobenius. It also states that restriction of continuous
`ℓ`-adic Galois representations to the Library's local Weil group preserves and reflects
intertwiners, isomorphism, irreducibility and finite models.
-/

noncomputable section

universe u uW

open CategoryTheory AlgebraicGeometry

namespace Langlands.Henniart.Laumon

open Langlands.Henniart.LocalNumerical

attribute [local instance] Langlands.LocalField.Laurent.valuativeRel

section Line

variable (k : Type u) [Field k]

/-- The structure map of the punctured end trait to `Spec k`, through the constants. -/
def puncturedEndToBase (e : FourierEnd) : puncturedEnd k e ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom ((endRing k).subtype.comp (endConstantHom k)))

variable [Finite k] (ℓ : ℕ) [Fact ℓ.Prime]

open Langlands.Weil.Local.SepClosed in
/-- The Weil scalar of an unramified character: its value on the image of the Library's
geometric Frobenius `localGeometricFrobenius`, a Weil element of degree one. -/
def unramifiedScalar
    (χ : ladicUnramifiedCharacters (LaurentSeries k) (SeparableClosure (LaurentSeries k)) ℓ) :
    (PadicAlgCl ℓ)ˣ :=
  χ.1 (localProjection (LaurentSeries k) (SeparableClosure (LaurentSeries k))
    (localGeometricFrobenius (LaurentSeries k) (SeparableClosure (LaurentSeries k))))

/-- A lisse sheaf on `Spec k` is a line for the scalar `c` when its stalk at
`Spec k̄ → Spec k` (`k̄ = AlgebraicClosure k`) has rank one and the Library's geometric
Frobenius `Galois.FiniteField.geometricFrobenius k` acts on it by `c`. -/
def IsUnramifiedLineFor (c : (PadicAlgCl ℓ)ˣ) (G : ProEtale.LisseSheaf ℓ (Spec (.of k))) : Prop :=
  Module.finrank (PadicAlgCl ℓ)
      (ProEtale.LisseMonodromy.StalkSpace (fieldGeometricPoint k (AlgebraicClosure k)) G) = 1 ∧
    ∀ v, fieldMonodromy ℓ k (AlgebraicClosure k) G
        (Galois.FiniteField.geometricFrobenius k : Gal(AlgebraicClosure k/k)) v = (c : PadicAlgCl ℓ) • v

open Classical in
/-- The arithmetic lisse line on `Spec k` of an unramified character `χ`: a lisse line on which
geometric Frobenius acts by the Weil scalar `unramifiedScalar k ℓ χ`, chosen when one exists,
and the constant sheaf otherwise. `UnramifiedLineMonodromyStatement` asserts that one exists. -/
def unramifiedLine
    (χ : ladicUnramifiedCharacters (LaurentSeries k) (SeparableClosure (LaurentSeries k)) ℓ) :
    ProEtale.LisseSheaf ℓ (Spec (.of k)) :=
  if h : ∃ G, IsUnramifiedLineFor k ℓ (unramifiedScalar k ℓ χ) G then h.choose
  else ProEtale.LisseSheaf.unit (Y := Spec (.of k)) ℓ

end Line

open Langlands.Weil.Local.SepClosed in
/-- **Unramified lines.** For every unramified character `χ`, `unramifiedLine k ℓ χ` is a lisse
line with geometric Frobenius acting by the Weil scalar; its pullback to every end trait has
monodromy `σ ↦ χ σ` on the separable generic closure, through `completionRestriction k`; and
`χ` takes the value `c ^ n` on Weil elements of degree `n`, `c` being the Weil scalar. -/
def UnramifiedLineMonodromyStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime]
    (χ : ladicUnramifiedCharacters (LaurentSeries k) (SeparableClosure (LaurentSeries k)) ℓ),
    IsUnramifiedLineFor k ℓ (unramifiedScalar k ℓ χ) (unramifiedLine k ℓ χ) ∧
    (∀ (e : FourierEnd) (σ : Gal(SeparableClosure (LaurentSeries k)/LaurentSeries k))
        (v : ProEtale.LisseMonodromy.StalkSpace
          (fieldGeometricPoint (endField k) (endGenericClosure k))
          ((unramifiedLine k ℓ χ).upperStar ℓ (puncturedEndToBase k e))),
      fieldMonodromy ℓ (endField k) (endGenericClosure k)
          ((unramifiedLine k ℓ χ).upperStar ℓ (puncturedEndToBase k e))
          (completionRestriction k σ) v = (χ.1 σ : PadicAlgCl ℓ) • v) ∧
    ∀ w : localWeilGroup (LaurentSeries k) (SeparableClosure (LaurentSeries k)),
      χ.1 (localProjection (LaurentSeries k) (SeparableClosure (LaurentSeries k)) w) =
        unramifiedScalar k ℓ χ ^ localDegreeInt (LaurentSeries k)
          (SeparableClosure (LaurentSeries k)) w

open Langlands.Weil.Local.SepClosed in
/-- **Restriction to the local Weil group.** For continuous finite-dimensional `ℓ`-adic
representations of the absolute Galois group of `LaurentSeries k`, restriction along the
Library's `localProjection` preserves and reflects intertwiners, isomorphism, irreducibility
and the finite-model condition `IsLadicDefinedOverFiniteExtension`. -/
def LocalWeilRestrictionStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime]
    (A B : FiniteRepresentation.{0, u, uW} (PadicAlgCl ℓ)
      Gal(SeparableClosure (LaurentSeries k)/LaurentSeries k)),
    IsLadicContinuous ℓ A → IsLadicContinuous ℓ B →
      (∀ f : A →ₗ[PadicAlgCl ℓ] B,
        (∀ σ v, f (A.representation σ v) = B.representation σ (f v)) ↔
          ∀ w v, f (A.representation
              (localProjection (LaurentSeries k) (SeparableClosure (LaurentSeries k)) w) v) =
            B.representation
              (localProjection (LaurentSeries k) (SeparableClosure (LaurentSeries k)) w) (f v)) ∧
      (FiniteRepresentation.IsIsomorphic A B ↔
        FiniteRepresentation.IsIsomorphic
          (FiniteRepresentation.restrict
            (localProjection (LaurentSeries k) (SeparableClosure (LaurentSeries k))).toMonoidHom A)
          (FiniteRepresentation.restrict
            (localProjection (LaurentSeries k) (SeparableClosure (LaurentSeries k))).toMonoidHom B)) ∧
      (Representation.IsIrreducible A.representation ↔
        Representation.IsIrreducible (FiniteRepresentation.restrict
          (localProjection (LaurentSeries k) (SeparableClosure (LaurentSeries k))).toMonoidHom
            A).representation) ∧
      (IsLadicDefinedOverFiniteExtension ℓ A ↔
        IsLadicDefinedOverFiniteExtension ℓ (FiniteRepresentation.restrict
          (localProjection (LaurentSeries k) (SeparableClosure (LaurentSeries k))).toMonoidHom A))

end Langlands.Henniart.Laumon
