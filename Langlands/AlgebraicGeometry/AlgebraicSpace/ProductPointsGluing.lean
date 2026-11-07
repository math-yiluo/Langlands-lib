import Langlands.AlgebraicGeometry.AlgebraicSpace.ProductPointsDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedProductPointsInjectiveProof
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Descending points of algebraic spaces along products of finite free extensions

Let `X` be an algebraic space over `Spec C`, and let `A i → B i` be a family of finite free
extensions of uniform rank `d ≥ 1`. Write `R = ∏ A i` and `R' = ∏ B i`. Then `Spec R' → Spec R`
is an fppf covering. If `X` is separated, a point `x' ∈ X(R')` descends to `X(R)` as soon as,
for every `i`, its two images in `X(B i ⊗[A i] B i)` agree. This is the descent step of Conrad's
proof of Proposition 5.2.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct Module
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (RingPoint ringTest ringTestMap ringTestMap_comp)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace ProductPointsDescent

section Cover

variable {S : Scheme.{u}} (X : AlgebraicSpace S) {T T' : Over S} (f : T' ⟶ T)
  [Flat f.left] [LocallyOfFinitePresentation f.left] [Surjective f.left]

/-- An algebraic space is a sheaf for a single fppf covering morphism. -/
theorem isSheafFor_singleton : Presieve.IsSheafFor X.presheaf (Presieve.singleton f) := by
  have hX := (isSheaf_iff_isSheaf_of_type _ _).mp X.toSheaf.property
  have hmem : Sieve.generate (Presieve.singleton f) ∈ fppfTopology S T :=
    mem_fppfTopology_of_mem _ f
      (Sieve.le_generate (Presieve.singleton f) T' f (Presieve.singleton_self f))
  exact (Presieve.isSheafFor_iff_generate _).mpr (hX _ hmem)

/-- Pullback of sections along an fppf covering morphism is injective. -/
theorem pullback_injective : Function.Injective (X.pullback f) :=
  Presieve.isSeparatedFor_singleton.mp (isSheafFor_singleton X f).isSeparatedFor

/-- A section over the source whose two pullbacks to the self-fibre product agree descends. -/
theorem exists_pullback_eq {P : Over S} {p₁ p₂ : P ⟶ T'} (hP : IsPullback p₁ p₂ f f)
    (x' : X.sections T') (hx : X.pullback p₁ x' = X.pullback p₂ x') :
    ∃ x : X.sections T, X.pullback f x = x' := by
  obtain ⟨x, hx', -⟩ := Presieve.isSheafFor_singleton.mp (isSheafFor_singleton X f) x'
    (fun {Z} q₁ q₂ hq => by
      obtain ⟨l, h₁, h₂⟩ : ∃ l : Z ⟶ P, l ≫ p₁ = q₁ ∧ l ≫ p₂ = q₂ :=
        ⟨hP.lift q₁ q₂ hq, hP.lift_fst _ _ _, hP.lift_snd _ _ _⟩
      change X.pullback q₁ x' = X.pullback q₂ x'
      rw [← h₁, ← h₂, pullback_comp, pullback_comp, hx])
  exact ⟨x, hx'⟩

end Cover

section FiniteFree

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] {d : ℕ}

/-- A finite free algebra of positive rank is faithfully flat. -/
theorem faithfullyFlat_of_basis [NeZero d] (b : Basis (Fin d) R R') : FaithfullyFlat R R' :=
  FaithfullyFlat.of_linearEquiv _ _ b.repr

/-- For a finite free algebra of positive rank, `Spec R' → Spec R` is flat, locally of finite
presentation and surjective. -/
theorem spec_properties [NeZero d] (b : Basis (Fin d) R R') :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧
      LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  have : FaithfullyFlat R R' := faithfullyFlat_of_basis b
  have : Module.Free R R' := Module.Free.of_basis b
  have : Module.Finite R R' := Module.Finite.of_basis b
  have : Module.FinitePresentation R R' :=
    Module.finitePresentation_of_projective R R'
  have hff : (algebraMap R R').FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have h := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R R'))).mpr hff
  refine ⟨h.1, ?_, h.2⟩
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

end FiniteFree

section Product

variable (C : Type u) [CommRing C] {ι : Type u} {A B : ι → Type u}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i, Algebra (A i) (B i)]
  [∀ i, Algebra C (A i)] [∀ i, Algebra C (B i)] [∀ i, IsScalarTower C (A i) (B i)]

/-- Change of coefficients is functorial. -/
theorem changeRing_changeRing {X : AlgebraicSpace (Spec (CommRingCat.of C))}
    {D E F : Type u} [CommRing D] [CommRing E] [CommRing F] [Algebra C D] [Algebra C E]
    [Algebra C F] (f : D →ₐ[C] E) (g : E →ₐ[C] F) (x : RingPoints C X D) :
    RingPoints.changeRing g (RingPoints.changeRing f x) = RingPoints.changeRing (g.comp f) x := by
  simp only [RingPoints.changeRing, ringTestMap_comp]
  exact (pullback_comp X _ _ x).symm

instance : IsScalarTower C (∀ i, A i) (∀ i, B i) :=
  ⟨fun c r y => funext fun i => smul_assoc c (r i) (y i)⟩

variable (A B) in
/-- The structure map `∏ A i → ∏ B i` over `C`. -/
abbrev πC : (∀ i, A i) →ₐ[C] (∀ i, B i) := IsScalarTower.toAlgHom C _ _

variable (A B) in
/-- The left inclusion into the tensor squares, over `C`. -/
def inlC : (∀ i, B i) →ₐ[C] TensorSquares A B :=
  { toRingHom := (inl A B).toRingHom
    commutes' := fun c => funext fun i => by
      change algebraMap C (B i) c ⊗ₜ[A i] (1 : B i) = algebraMap C (B i ⊗[A i] B i) c
      rfl }

variable (A B) in
/-- The right inclusion into the tensor squares, over `C`. -/
def inrC : (∀ i, B i) →ₐ[C] TensorSquares A B :=
  { toRingHom := (inr A B).toRingHom
    commutes' := fun c => funext fun i => by
      change (1 : B i) ⊗ₜ[A i] algebraMap C (B i) c = algebraMap C (B i ⊗[A i] B i) c
      rw [IsScalarTower.algebraMap_apply C (A i) (B i), Algebra.algebraMap_eq_smul_one,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one,
        ← IsScalarTower.algebraMap_apply]
      rfl }

/-- The square of spectra of `∏ A i → ∏ B i ⇉ ∏ (B i ⊗ B i)` is a pullback over `Spec C`. -/
theorem isPullback_tensorSquares {d : ℕ} (b : ∀ i, Basis (Fin d) (A i) (B i)) :
    IsPullback (ringTestMap C (inlC C A B)) (ringTestMap C (inrC C A B))
      (ringTestMap C (πC C A B)) (ringTestMap C (πC C A B)) := by
  let e : ((∀ i, B i) ⊗[∀ i, A i] (∀ i, B i)) ≃+* TensorSquares A B :=
    RingEquiv.ofBijective (comparison A B).toRingHom (comparison_bijective b)
  have hpo := (CommRingCat.isPushout_tensorProduct (∀ i, A i) (∀ i, B i) (∀ i, B i)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso
    (f' := CommRingCat.ofHom (πC C A B).toRingHom)
    (g' := CommRingCat.ofHom (πC C A B).toRingHom)
    (inl' := CommRingCat.ofHom (inlC C A B).toRingHom)
    (inr' := CommRingCat.ofHom (inrC C A B).toRingHom)
    (by ext; rfl) (by ext; rfl)
    (CommRingCat.hom_ext (RingHom.ext fun x => by
      change comparison A B (x ⊗ₜ 1) = inl A B x
      funext i
      rw [comparison_tmul]
      rfl))
    (CommRingCat.hom_ext (RingHom.ext fun x => by
      change comparison A B (1 ⊗ₜ x) = inr A B x
      funext i
      rw [comparison_tmul]
      rfl))
  have hsp : IsPullback
      ((Over.forget (Spec (CommRingCat.of C))).map (ringTestMap C (inlC C A B)))
      ((Over.forget (Spec (CommRingCat.of C))).map (ringTestMap C (inrC C A B)))
      ((Over.forget (Spec (CommRingCat.of C))).map (ringTestMap C (πC C A B)))
      ((Over.forget (Spec (CommRingCat.of C))).map (ringTestMap C (πC C A B))) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  exact hsp.of_map_of_faithful (Over.forget (Spec (CommRingCat.of C)))

/-- **Descent of points along products of finite free extensions.** For a separated
algebraic space `X` over `Spec C` and finite free extensions `A i → B i` of uniform rank
`d ≥ 1`, a point of `X` with values in `∏ B i` comes from `∏ A i` as soon as, for every `i`,
its two images in `X(B i ⊗[A i] B i)` agree. -/
theorem exists_changeRing_eq {X : AlgebraicSpace (Spec (CommRingCat.of C))}
    (hX : IsSeparated X) {d : ℕ} [NeZero d] (b : ∀ i, Basis (Fin d) (A i) (B i))
    (x' : RingPoints C X (∀ i, B i))
    (hx : ∀ i, RingPoints.changeRing ((Pi.evalAlgHom C _ i).comp (inlC C A B)) x' =
      RingPoints.changeRing ((Pi.evalAlgHom C _ i).comp (inrC C A B)) x') :
    ∃ x : RingPoints C X (∀ i, A i), RingPoints.changeRing (πC C A B) x = x' := by
  obtain ⟨h₁, h₂, h₃⟩ := spec_properties (piBasis b)
  have : Flat (ringTestMap C (πC C A B)).left := h₁
  have : LocallyOfFinitePresentation (ringTestMap C (πC C A B)).left := h₂
  have : Surjective (ringTestMap C (πC C A B)).left := h₃
  have heq : RingPoints.changeRing (inlC C A B) x' = RingPoints.changeRing (inrC C A B) x' := by
    apply separatedProductPoints_injective C X hX ι (fun i => B i ⊗[A i] B i)
    funext i
    simp only [changeRing_changeRing]
    exact hx i
  exact exists_pullback_eq X (ringTestMap C (πC C A B)) (isPullback_tensorSquares C b) x' heq

end Product

end ProductPointsDescent

end Langlands.AlgebraicGeometry.AlgebraicSpace
