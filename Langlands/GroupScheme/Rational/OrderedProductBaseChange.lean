import Langlands.GroupScheme.Rational.OrderedProductMaps
import Langlands.GroupScheme.BaseChangeReflection

/-! # Base change and fpqc detection of the original ordered multiplication -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B C : Scheme.{u}} (b : C ⟶ B)

section FiniteProducts

variable {I : Type v} [Finite I] (H : I → GroupScheme B)

/-- Pullback of the underlying finite-product fan is limiting. -/
def finiteProductBaseChangeIsLimit :
    IsLimit (Fan.mk ((GroupScheme.baseChange b).obj (∏ᶜ H)).X
      fun i => ((GroupScheme.baseChange b).map (Pi.π H i)).hom.hom) :=
  isLimitFanMkObjOfIsLimit (Over.pullback b) (fun i => (H i).X)
    (fun i => (Pi.π H i).hom.hom) (finiteProductIsLimit H)

/-- The canonical comparison between the pullback of a finite product and
the finite product of the actual pullbacks. -/
def finiteProductBaseChangeIso :
    ((GroupScheme.baseChange b).obj (∏ᶜ H)).X ≅
      (∏ᶜ fun i => (GroupScheme.baseChange b).obj (H i)).X :=
  (finiteProductBaseChangeIsLimit b H).conePointUniqueUpToIso
    (finiteProductIsLimit (fun i => (GroupScheme.baseChange b).obj (H i)))

@[reassoc (attr := simp)]
theorem finiteProductBaseChangeIso_hom_π (i : I) :
    (finiteProductBaseChangeIso b H).hom ≫
        (Pi.π (fun i => (GroupScheme.baseChange b).obj (H i)) i).hom.hom =
      ((GroupScheme.baseChange b).map (Pi.π H i)).hom.hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

@[reassoc (attr := simp)]
theorem finiteProductBaseChangeIso_inv_π (i : I) :
    (finiteProductBaseChangeIso b H).inv ≫
        ((GroupScheme.baseChange b).map (Pi.π H i)).hom.hom =
      (Pi.π (fun i => (GroupScheme.baseChange b).obj (H i)) i).hom.hom :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

end FiniteProducts

section OrderedMultiplication

variable {n : ℕ} {G : GroupScheme B} {H : Fin n → GroupScheme B}
    (j : ∀ i, H i ⟶ G)

private theorem pullback_list_prod {X : Over B} (l : List (X ⟶ G.X)) :
    (Over.pullback b).map l.prod =
      (l.map (fun f => (show (Over.pullback b).obj X ⟶
        ((GroupScheme.baseChange b).obj G).X from (Over.pullback b).map f))).prod := by
  induction l with
  | nil => exact (Over.pullback b).map_one
  | cons x l ih =>
      simp only [List.prod_cons, List.map_cons, Functor.map_mul, ih]

/-- The base-changed ordered multiplication is the original ordered
multiplication of the pulled-back factors, after the canonical product comparison. -/
theorem orderedMultiplication_baseChange :
    (finiteProductBaseChangeIso b H).hom ≫
        orderedMultiplication (fun i => (GroupScheme.baseChange b).map (j i)) =
      (Over.pullback b).map (orderedMultiplication j) := by
  rw [comp_orderedMultiplication]
  unfold orderedMultiplication orderedPoints
  rw [pullback_list_prod]
  simp only [List.map_ofFn, Function.comp_def, Functor.map_comp]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  simp only [finiteProductPointsEquiv_apply,
    finiteProductBaseChangeIso_hom_π]
  rfl

/-- Invertibility of ordered multiplication is preserved by arbitrary base change. -/
theorem isIso_orderedMultiplication_baseChange [IsIso (orderedMultiplication j)] :
    IsIso (orderedMultiplication (fun i => (GroupScheme.baseChange b).map (j i))) := by
  have h : orderedMultiplication (fun i => (GroupScheme.baseChange b).map (j i)) =
      (finiteProductBaseChangeIso b H).inv ≫
        (Over.pullback b).map (orderedMultiplication j) := by
    rw [← orderedMultiplication_baseChange b j, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- Invertibility of the original ordered multiplication descends along an fpqc
base morphism. This is an assertion about actual scheme morphisms. -/
theorem isIso_orderedMultiplication_of_baseChange
    [Surjective b] [Flat b] [QuasiCompact b]
    [IsIso (orderedMultiplication (fun i => (GroupScheme.baseChange b).map (j i)))] :
    IsIso (orderedMultiplication j) := by
  let f := orderedMultiplication j
  have : IsIso ((Over.pullback b).map f) := by
    rw [← orderedMultiplication_baseChange b j]
    infer_instance
  have : IsIso ((Over.pullback b).map f).left :=
    inferInstanceAs (IsIso ((Over.forget C).map ((Over.pullback b).map f)))
  have houter : IsPullback
      (((Over.pullback b).map f).left ≫ pullback.snd G.X.hom b)
      (pullback.fst (∏ᶜ H).X.hom b) b (f.left ≫ G.X.hom) := by
    simpa only [Over.w f, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback (∏ᶜ H).X.hom b).flip
  have hp := houter.of_right
    (show ((Over.pullback b).map f).left ≫ pullback.fst G.X.hom b =
        pullback.fst (∏ᶜ H).X.hom b ≫ f.left by
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback G.X.hom b).flip
  have : IsIso f.left :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have : IsIso ((Over.forget B).map f) := by
    change IsIso f.left
    infer_instance
  exact isIso_of_reflects_iso f (Over.forget B)

/-- An fpqc base morphism detects exactly whether the specified original
ordered multiplication is an isomorphism, including the empty product. -/
theorem isIso_orderedMultiplication_baseChange_iff
    [Surjective b] [Flat b] [QuasiCompact b] :
    IsIso (orderedMultiplication (fun i => (GroupScheme.baseChange b).map (j i))) ↔
      IsIso (orderedMultiplication j) :=
  ⟨fun h => letI := h; isIso_orderedMultiplication_of_baseChange b j,
    fun h => letI := h; isIso_orderedMultiplication_baseChange b j⟩

end OrderedMultiplication

section FieldExtension

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {n : ℕ} {G : GroupScheme (Spec (CommRingCat.of k))}
    {H : Fin n → GroupScheme (Spec (CommRingCat.of k))}

/-- A field extension detects the original ordered multiplication isomorphism. -/
theorem isIso_orderedMultiplication_fieldExtension_iff (j : ∀ i, H i ⟶ G) :
    IsIso (orderedMultiplication (fun i =>
      (GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map (j i))) ↔
      IsIso (orderedMultiplication j) := by
  obtain ⟨hs, hf, hqc⟩ := fieldExtension_fpqc k K
  let := hs
  let := hf
  let := hqc
  exact isIso_orderedMultiplication_baseChange_iff
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) j

end FieldExtension

end Langlands.GroupScheme.RelativeRoot
