/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.CategoryTheory.Abelian.HorseshoePrescribedResolutions

/-!
# Compatible injective resolutions of a short exact sequence

Source: Stacks Project, Derived Categories, Lemma 13.18.9 (Tag 013T), parts (2)-(3),
applied to objects concentrated in degree zero, and proof Steps 1-2
(blueprint: lem-weil-pbc-injective-resolution-ses).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveResolution

/-- A short exact sequence in an abelian category with enough injectives admits three
compatible injective resolutions with short exact rows in every nonnegative degree.
The middle terms can be identified with biproducts so that the row maps are the first
inclusion and second projection. Natural-number indexing represents extension by zero
in every negative degree. The augmentation equalities are equalities of complex maps;
their only nonzero source component is in degree zero.

Source: Stacks Project, Derived Categories, Lemma 13.18.9 (Tag 013T), parts (2)-(3),
for the complexes A[0], B[0], C[0], proof Steps 1-2
(blueprint: lem-weil-pbc-injective-resolution-ses).

Proof, Step 1: choose embeddings A -> I_A^0 and C -> I_C^0 into injectives
(def-sp-injective-resolutions). Push out A -> B along A -> I_A^0. In the abelian
category (def-sp-abelian) the resulting sequence I_A^0 -> P -> C is short exact.
Since I_A^0 is injective this sequence splits. Identify P with I_A^0 biproduct C
and embed it into I_A^0 biproduct I_C^0. The composite embedding of B gives the
middle augmentation, and the degree-zero augmentation squares commute.
Step 2: take the cokernels of these three embeddings. The commutative diagram with
short exact rows induces a short exact sequence of cokernels. Repeat Step 1 with
these cokernels, choosing embeddings into I_A^1 and I_C^1. The quotient maps followed
by the new embeddings give the differentials. Inductively repeat this construction
in every degree (def-sp-abelian, def-sp-injective-resolutions).
Step 3: the compatible cokernel diagrams make the inclusions and projections commute
with the differentials, so they are complex maps. At every degree their row is the
split biproduct sequence. Each augmented complex is exact: its differential factors
as the preceding cokernel map followed by an embedding, so its kernel is the preceding
image. The degree-zero kernel is the original object. Biproducts of the two injectives
are injective, so all three complexes are injective resolutions; extending by zero
in negative degrees gives the required bounds (def-sp-injective-resolutions).
Step 4: all choices use only enough injectives; the augmentation squares, degreewise
short exactness, and biproduct identifications give every asserted compatibility. -/
theorem exists_horseshoe_resolutions
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (S : ShortComplex C) (hS : S.ShortExact) :
    ∃ (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
      (IC : InjectiveResolution S.X₃)
      (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex),
      IA.ι ≫ α = (CochainComplex.single₀ C).map S.f ≫ IB.ι ∧
      IB.ι ≫ β = (CochainComplex.single₀ C).map S.g ≫ IC.ι ∧
      ∃ (hαβ : α ≫ β = 0), ∀ n : ℕ,
        ((ShortComplex.mk α β hαβ).map
          (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact ∧
        ∃ e : IB.cocomplex.X n ≅ IA.cocomplex.X n ⊞ IC.cocomplex.X n,
        α.f n ≫ e.hom = biprod.inl ∧ β.f n = e.hom ≫ biprod.snd := by
  let IA : InjectiveResolution S.X₁ := InjectiveResolution.of S.X₁
  let IC : InjectiveResolution S.X₃ := InjectiveResolution.of S.X₃
  obtain ⟨IB, α, β, hα, hβ, hrows⟩ :=
    InjectiveResolution.exists_horseshoe_prescribed_resolutions S hS IA IC
  exact ⟨IA, IB, IC, α, β, hα, hβ, hrows⟩

end CategoryTheory.InjectiveResolution
