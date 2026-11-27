import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPoints

/-!
# Elementary étale points of separated algebraic spaces

For a separated algebraic space `X` over a field `K`, every point of `X` in the image of an
étale point `Spec A → X` of a finite type `K`-algebra `A` is also the image of a point `q` of
an étale point `Spec B → X` of a finite type `K`-algebra `B` at which `Spec B → X` is
elementary: the image of `q` under the diagonal is the only point of `Spec B ×_X Spec B` lying
over `q` under both projections. This is a ring-point form of Stacks Project, Decent Algebraic
Spaces, Lemma 68.11.4 (Tag 0BBP), for separated spaces.
-/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTestMap)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Elementary étale points of separated algebraic spaces over a field (a ring-point form of
Stacks, Tag 0BBP). Let `X` be a separated algebraic space over `Spec K`, `x : Spec A → X` an
étale point of a finite type `K`-algebra `A` and `p` a prime of `A`. Then there are a finite
type `K`-algebra `B`, an étale point `y : Spec B → X` and a prime `q` of `B` such that
1. `q` and `p` have the same image in `|X|`: whenever `Spec D` with the maps of spectra of
   `f : B → D` and `g : A → D` is a fibre product `Spec B ×_X Spec A` of presheaves, some
   prime of `D` contracts to `q` along `f` and to `p` along `g`;
2. `y` is elementary at `q`: whenever `Spec C` with the maps of spectra of `f g : B → C` is a
   fibre product `Spec B ×_X Spec B` and `μ : C → B` is a `K`-algebra map with
   `μ ∘ f = μ ∘ g = id` (the diagonal), the only prime of `C` contracting to `q` along both
   `f` and `g` is `μ⁻¹(q)`. -/
def SeparatedElementaryEtalePointStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : AlgebraicSpace (Spec (CommRingCat.of K))), IsSeparated X →
    ∀ (A : Type u) [CommRing A] [Algebra K A], Algebra.FiniteType K A →
    ∀ x : RingPoints K X A, IsEtale (uliftYonedaEquiv.{u + 1}.symm x) →
    ∀ p : PrimeSpectrum A,
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra K B) (_ : Algebra.FiniteType K B)
        (y : RingPoints K X B) (q : PrimeSpectrum B),
        IsEtale (uliftYonedaEquiv.{u + 1}.symm y) ∧
        (∀ (D : Type u) [CommRing D] [Algebra K D] (f : B →ₐ[K] D) (g : A →ₐ[K] D),
          IsPullback ((schemeYoneda (Spec (CommRingCat.of K))).map (ringTestMap K f))
              ((schemeYoneda (Spec (CommRingCat.of K))).map (ringTestMap K g))
              (uliftYonedaEquiv.{u + 1}.symm y) (uliftYonedaEquiv.{u + 1}.symm x) →
            ∃ P : PrimeSpectrum D,
              PrimeSpectrum.comap (f : B →+* D) P = q ∧ PrimeSpectrum.comap (g : A →+* D) P = p) ∧
        ∀ (C : Type u) [CommRing C] [Algebra K C] (f g : B →ₐ[K] C),
          IsPullback ((schemeYoneda (Spec (CommRingCat.of K))).map (ringTestMap K f))
              ((schemeYoneda (Spec (CommRingCat.of K))).map (ringTestMap K g))
              (uliftYonedaEquiv.{u + 1}.symm y) (uliftYonedaEquiv.{u + 1}.symm y) →
            ∀ μ : C →ₐ[K] B, μ.comp f = AlgHom.id K B → μ.comp g = AlgHom.id K B →
              ∀ P : PrimeSpectrum C, PrimeSpectrum.comap (f : B →+* C) P = q →
                PrimeSpectrum.comap (g : B →+* C) P = q →
                  P = PrimeSpectrum.comap (μ : C →+* B) q

end Langlands.AlgebraicGeometry.AlgebraicSpace
