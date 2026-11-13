import Langlands.AlgebraicGeometry.Picard.ArtinianResidueCohomology
import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackCoefficientNaturalityProof

/-! # Canonical cohomology pullback in finite-product coordinates -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.FiniteProductCohomologyPullback

open Langlands.AlgebraicGeometry.Modules.DerivedSections
  PicardGroupoid.ArtinianResidueCohomology

variable {R : CommRingCat.{u}} {X Y : Over (Spec R)} (f : Y ⟶ X)
  (M : X.left.Modules) (N : Y.left.Modules)

/-- Canonical cohomology pullback followed by the given coefficient morphism. -/
def coefficientPull (a : (Scheme.Modules.pullback f.left).obj M ⟶ N) (n : ℕ) :
    (relativeCohomology X.hom n).obj M ⟶
      (relativeCohomology Y.hom n).obj N :=
  relativeCohomologyPullback f M n ≫ (relativeCohomology Y.hom n).map a

/-- Coordinatewise coefficient pullback into the actual product sheaf. -/
def productCoefficient (ι : Type u)
    (a : (Scheme.Modules.pullback f.left).obj M ⟶ N) :
    (Scheme.Modules.pullback f.left).obj (∏ᶜ fun _ : ι => M) ⟶
      ∏ᶜ fun _ : ι => N :=
  Pi.lift fun j => (Scheme.Modules.pullback f.left).map (Pi.π (fun _ : ι => M) j) ≫ a

@[reassoc]
lemma productCoefficient_π (ι : Type u)
    (a : (Scheme.Modules.pullback f.left).obj M ⟶ N) (j : ι) :
    productCoefficient f M N ι a ≫ Pi.π (fun _ : ι => N) j =
      (Scheme.Modules.pullback f.left).map (Pi.π (fun _ : ι => M) j) ≫ a := by
  simp [productCoefficient]

variable {M N}

/-- A commuting square of coefficient morphisms gives its actual cohomology square. -/
@[reassoc]
lemma coefficientPull_naturality
    {M' : X.left.Modules} {N' : Y.left.Modules}
    (a : (Scheme.Modules.pullback f.left).obj M ⟶ N)
    (a' : (Scheme.Modules.pullback f.left).obj M' ⟶ N')
    (b : M ⟶ M') (c : N ⟶ N')
    (h : (Scheme.Modules.pullback f.left).map b ≫ a' = a ≫ c) (n : ℕ) :
    (relativeCohomology X.hom n).map b ≫ coefficientPull f M' N' a' n =
      coefficientPull f M N a n ≫ (relativeCohomology Y.hom n).map c := by
  unfold coefficientPull
  rw [← Category.assoc, relativeCohomologyPullback_naturality]
  rw [Category.assoc, ← Functor.map_comp, h, Functor.map_comp]
  simp only [Category.assoc]

variable (M N)

/-- The existing finite-product cohomology coordinates intertwine the actual
canonical pullback and its coordinatewise coefficient morphism. -/
lemma finiteProductCohomologyIso_pull (ι : Type u) [Finite ι]
    (a : (Scheme.Modules.pullback f.left).obj M ⟶ N) (n : ℕ)
    (x : (relativeCohomology X.hom n).obj (∏ᶜ fun _ : ι => M)) (j : ι) :
    (finiteProductCohomologyIso Y.hom N ι n).hom
        (coefficientPull f (∏ᶜ fun _ : ι => M) (∏ᶜ fun _ : ι => N)
          (productCoefficient f M N ι a) n x) j =
      coefficientPull f M N a n ((finiteProductCohomologyIso X.hom M ι n).hom x j) := by
  rw [finiteProductCohomologyIso_apply, finiteProductCohomologyIso_apply]
  have h := coefficientPull_naturality f (productCoefficient f M N ι a) a
    (Pi.π (fun _ : ι => M) j) (Pi.π (fun _ : ι => N) j)
    (productCoefficient_π f M N ι a j).symm n
  exact (congrArg (fun q => q x) h).symm

/-- Transporting two modules to actual finite products gives the same
coordinatewise formula once the sheaf-level coefficient square commutes. -/
lemma finiteProductCohomologyIso_transport_pull
    (P : X.left.Modules) (Q : Y.left.Modules) (ι : Type u) [Finite ι]
    (eX : M ≅ ∏ᶜ fun _ : ι => P) (eY : N ≅ ∏ᶜ fun _ : ι => Q)
    (a : (Scheme.Modules.pullback f.left).obj M ⟶ N)
    (c : (Scheme.Modules.pullback f.left).obj P ⟶ Q)
    (h : (Scheme.Modules.pullback f.left).map eX.hom ≫
        productCoefficient f P Q ι c = a ≫ eY.hom)
    (n : ℕ) (x : (relativeCohomology X.hom n).obj M) (j : ι) :
    (finiteProductCohomologyIso Y.hom Q ι n).hom
        ((relativeCohomology Y.hom n).map eY.hom
          (coefficientPull f M N a n x)) j =
      coefficientPull f P Q c n
        ((finiteProductCohomologyIso X.hom P ι n).hom
          ((relativeCohomology X.hom n).map eX.hom x) j) := by
  have hn := coefficientPull_naturality f a (productCoefficient f P Q ι c)
    eX.hom eY.hom h n
  have hx := congrArg (fun q => q x) hn
  change coefficientPull f (∏ᶜ fun _ : ι => P) (∏ᶜ fun _ : ι => Q)
      (productCoefficient f P Q ι c) n
      ((relativeCohomology X.hom n).map eX.hom x) =
    (relativeCohomology Y.hom n).map eY.hom (coefficientPull f M N a n x) at hx
  rw [← hx]
  exact finiteProductCohomologyIso_pull f P Q ι c n _ j

end Langlands.AlgebraicGeometry.Picard.FiniteProductCohomologyPullback
