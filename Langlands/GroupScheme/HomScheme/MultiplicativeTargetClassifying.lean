import Langlands.GroupScheme.HomScheme.MultiplicativeTargetEtale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Étale classifying neighbourhoods for homomorphisms from a finite diagonalizable group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme

open Langlands.FiniteBialgebraHom FiniteSource FiniteDiagonalizable

section Flatness

instance lfp_isMultiplicative :
    MorphismProperty.IsMultiplicative (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
    where
  id_mem _ := inferInstance

instance : MorphismProperty.HasOfPostcompProperty
    (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) @Etale := by
  rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
  intro X Y f hf
  have : Etale f := hf
  exact ⟨inferInstanceAs (Flat (pullback.diagonal f)),
    inferInstanceAs (LocallyOfFinitePresentation (pullback.diagonal f))⟩

/-- A morphism whose composite with an étale morphism is flat and locally of finite
presentation is itself flat and locally of finite presentation. -/
theorem flat_lfp_of_comp_etale {W Y X : Scheme.{u}} (c : W ⟶ Y) (p : Y ⟶ X) [Etale p]
    [Flat (c ≫ p)] [LocallyOfFinitePresentation (c ≫ p)] :
    Flat c ∧ LocallyOfFinitePresentation c :=
  MorphismProperty.of_postcomp (W := @Flat ⊓ @LocallyOfFinitePresentation) (W' := @Etale)
    c p inferInstance ⟨inferInstance, inferInstance⟩

end Flatness

section Universal

variable {R : Type u} [CommRing R]

variable (R) in
/-- The diagonalizable group `D(A)` over `Spec R` as the Hopf spectrum of `R[A]`. -/
def sourceModelIso (A : Type u) [AddCommGroup A] :
    RelativeMultiplicativeType.diagonalizable (Spec (CommRingCat.of R)) A ≅
      hopfGroup R (AddMonoidAlgebra R A) :=
  (Diagonalizable.hopfSpecIso (CommRingCat.of R) A ≪≫
    Diagonalizable.relativeModelIso (CommRingCat.of R) A).symm

/-- The universal homomorphism from `D(A)` to an affine group `G` of finite presentation. -/
def universalHom (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
    [LocallyOfFinitePresentation G.X.hom] (A : Type u) [AddCommGroup A] [Fintype A] :
    RelativeHom (RelativeMultiplicativeType.diagonalizable (Spec (CommRingCat.of R)) A) G
      (specOver R (HomAlgebra R (AffineCoordinates.hopfAlgebra G) (AddMonoidAlgebra R A))) :=
  transport (sourceModelIso R A) (coordinateIso G) (universalFamily R _ _)

theorem isUniversal_universalHom (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
    [LocallyOfFinitePresentation G.X.hom] (A : Type u) [AddCommGroup A] [Fintype A] :
    IsUniversal (universalHom G A) :=
  (isUniversal_universalFamily R _ _).transport _ _

theorem etale_specOver_hom (P : Type u) [CommRing P] [Algebra R P] [Algebra.Etale R P] :
    Etale (specOver R P).hom := by
  change Etale (Spec.map (CommRingCat.ofHom (algebraMap R P)))
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr inferInstance

end Universal

section Coherence

open RelativeMultiplicativeType

/-- The base-change isomorphism of `D(A)` is the canonical comparison of iterated base
changes from `Spec ℤ`. -/
theorem diagonalizableBaseChangeIso_eq {S S' : Scheme.{u}} (b : S' ⟶ S) (A : Type u)
    [AddCommGroup A] :
    diagonalizableBaseChangeIso b A =
      Descent.pullbackComparison (Gm.toSpecZ S) b (Gm.toSpecZ S')
        (specULiftZIsTerminal.hom_ext _ _)
        (Diagonalizable.groupScheme (CommRingCat.of (ULift.{u} ℤ)) A).toGrp :=
  rfl

/-- The base-change isomorphisms of `D(A)` are compatible with the comparison of iterated
base changes. -/
theorem diagonalizableBaseChangeIso_comparison {S X U : Scheme.{u}} (f : X ⟶ S) (q : U ⟶ X)
    (r : U ⟶ S) (hq : q ≫ f = r) (A : Type u) [AddCommGroup A] :
    (baseChange q).map (diagonalizableBaseChangeIso f A).inv ≫
        (Descent.pullbackComparison f q r hq (diagonalizable S A)).hom ≫
          (diagonalizableBaseChangeIso r A).hom =
      (diagonalizableBaseChangeIso q A).hom := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext ?_ ((Over.w ((baseChange q).map (diagonalizableBaseChangeIso f A).inv ≫
        (Descent.pullbackComparison f q r hq (diagonalizable S A)).hom ≫
          (diagonalizableBaseChangeIso r A).hom).hom.hom).trans
      (Over.w (diagonalizableBaseChangeIso q A).hom.hom.hom).symm)
  simp only [diagonalizableBaseChangeIso_eq, Grp.comp_hom_hom, Over.comp_left, Category.assoc]
  rw [Descent.pullbackComparison_hom_fst, Descent.pullbackComparison_hom_fst_assoc,
    baseChange_map_left_fst_assoc, Descent.pullbackComparison_inv_fst,
    Descent.pullbackComparison_hom_fst]

end Coherence

section Classifying

open RelativeMultiplicativeType

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

theorem flat_specBase [Module.Flat R R'] : Flat (specBase R R') := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

theorem lfp_specBase [Algebra.FinitePresentation R R'] :
    LocallyOfFinitePresentation (specBase R R') := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

theorem surjective_specBase [Module.FaithfullyFlat R R'] : Surjective (specBase R R') := by
  rw [surjective_iff]
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := R')

/-- **Étale classifying neighbourhood.** Let `G` be an affine group of finite presentation
over `Spec R` that is diagonalizable after a faithfully flat finitely presented `R → R'`, and
let `φ₀ : D(A) → G` be a homomorphism over `Spec R'`, for a finite abelian group `A`. Then
`Spec R' → Spec R` factors through an étale `X → Spec R` by a surjective flat morphism `q`
locally of finite presentation, and `φ₀` descends to a homomorphism `σ : D(A) → G` over
`X`. -/
theorem exists_etale_classifying [Module.FaithfullyFlat R R'] [Algebra.FinitePresentation R R']
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
    [LocallyOfFinitePresentation G.X.hom] {Λ : Type u} [AddCommGroup Λ]
    (ψ : (baseChange (specBase R R')).obj G ≅ diagonalizable (Spec (CommRingCat.of R')) Λ)
    (A : Type u) [AddCommGroup A] [Fintype A]
    (φ₀ : diagonalizable (Spec (CommRingCat.of R')) A ⟶ (baseChange (specBase R R')).obj G) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R)) (q : Spec (CommRingCat.of R') ⟶ X)
      (hq : q ≫ f = specBase R R'), Etale f ∧ Surjective q ∧ Flat q ∧
        LocallyOfFinitePresentation q ∧ ∃ σ : diagonalizable X A ⟶ (baseChange f).obj G,
          (diagonalizableBaseChangeIso q A).inv ≫ (baseChange q).map σ ≫
            (Descent.pullbackComparison f q (specBase R R') hq G).hom = φ₀ := by
  classical
  have : Algebra.Etale R
      (HomAlgebra R (AffineCoordinates.hopfAlgebra G) (AddMonoidAlgebra R A)) :=
    etale_homAlgebra G ψ A
  let Y := specOver R (HomAlgebra R (AffineCoordinates.hopfAlgebra G) (AddMonoidAlgebra R A))
  have hY : Etale Y.hom := etale_specOver_hom _
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (specBase R R')
  let f₀ : RelativeHom (diagonalizable (Spec (CommRingCat.of R)) A) G T :=
    (diagonalizableBaseChangeIso (specBase R R') A).hom ≫ φ₀
  obtain ⟨c, hc, -⟩ := (isUniversal_universalHom G A).existsUnique f₀
  have hcw : c.left ≫ Y.hom = specBase R R' := Over.w c
  have : Flat (specBase R R') := flat_specBase
  have : LocallyOfFinitePresentation (specBase R R') := lfp_specBase
  have : Flat (c.left ≫ Y.hom) := by rw [hcw]; infer_instance
  have : LocallyOfFinitePresentation (c.left ≫ Y.hom) := by rw [hcw]; infer_instance
  obtain ⟨hcf, hcl⟩ := flat_lfp_of_comp_etale c.left Y.hom
  have hopen : IsOpenMap c.left.base :=
    isOpenMap_of_generalizingMap c.left (Flat.generalizingMap c.left)
  let O : Y.left.Opens := ⟨Set.range c.left.base, hopen.isOpen_range⟩
  let q : Spec (CommRingCat.of R') ⟶ O := IsOpenImmersion.lift O.ι c.left (by simp [O]; exact fun _ h => h)
  have hq' : q ≫ O.ι = c.left := IsOpenImmersion.lift_fac _ _ _
  have hq : q ≫ (O.ι ≫ Y.hom) = specBase R R' := by rw [← Category.assoc, hq', hcw]
  have hqfl : Flat q ∧ LocallyOfFinitePresentation q :=
    MorphismProperty.of_postcomp (W := @Flat ⊓ @LocallyOfFinitePresentation) (W' := @Etale)
      q O.ι inferInstance (by rw [hq']; exact ⟨hcf, hcl⟩)
  have hqsurj : Surjective q := ⟨fun ⟨x, ⟨y, hy⟩⟩ => ⟨y, by
      apply O.ι.isOpenEmbedding.injective
      change (q ≫ O.ι) y = x
      rw [hq']
      exact hy⟩⟩
  let Xo : Over (Spec (CommRingCat.of R)) := Over.mk (O.ι ≫ Y.hom)
  let ι' : Xo ⟶ Y := Over.homMk O.ι rfl
  let q' : T ⟶ Xo := Over.homMk q hq
  have hqc : q' ≫ ι' = c := Over.OverMorphism.ext hq'
  let σr : RelativeHom (diagonalizable (Spec (CommRingCat.of R)) A) G Xo :=
    evaluate ι' (universalHom G A)
  refine ⟨O, O.ι ≫ Y.hom, q, hq, inferInstance, hqsurj, hqfl.1, hqfl.2,
    (diagonalizableBaseChangeIso (O.ι ≫ Y.hom) A).inv ≫ σr, ?_⟩
  have key : evaluate q' σr = f₀ := by
    simp only [σr]
    rw [← evaluate_comp, hqc, hc]
  have key' : (baseChange q).map σr ≫
      (Descent.pullbackComparison (O.ι ≫ Y.hom) q (specBase R R') hq G).hom =
      (Descent.pullbackComparison (O.ι ≫ Y.hom) q (specBase R R') hq
          (diagonalizable (Spec (CommRingCat.of R)) A)).hom ≫
        (diagonalizableBaseChangeIso (specBase R R') A).hom ≫ φ₀ := by
    rw [← Iso.inv_comp_eq]
    exact key
  have hcoh := congrArg (· ≫ φ₀)
    (diagonalizableBaseChangeIso_comparison (O.ι ≫ Y.hom) q (specBase R R') hq A)
  simp only [Category.assoc] at hcoh
  rw [Functor.map_comp, Category.assoc, key', hcoh, Iso.inv_hom_id_assoc]

end Classifying

end Langlands.GroupScheme.HomScheme
