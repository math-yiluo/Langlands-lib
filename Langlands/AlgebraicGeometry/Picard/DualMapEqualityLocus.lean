import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedProof
import Langlands.AlgebraicGeometry.Picard.DualScheme
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedForgetLocallySurjective
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-! # Closed equality loci for actual maps into a chosen dual -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

namespace DualMapEquality

variable {S : Scheme.{u}} (B : AbelianScheme S)

/-- The abelian self-product, with the actual fibre product as its carrier. -/
def square : AbelianScheme S where
  toGrp := B.toGrp ⊗ B.toGrp
  comm := inferInstanceAs (IsCommMonObj (B.X ⊗ B.X))
  smooth := by
    change Smooth (pullback.fst B.X.hom B.X.hom ≫ B.X.hom)
    infer_instance
  proper := by
    change IsProper (pullback.fst B.X.hom B.X.hom ≫ B.X.hom)
    infer_instance
  geometricallyConnected := by
    change GeometricallyConnected (pullback.fst B.X.hom B.X.hom ≫ B.X.hom)
    exact GeometricallyConnected.comp _ _

/-- The second-coordinate-zero axis of the self-product. -/
abbrev axis : B.X.left ⟶ (square B).X.left :=
  (relativeSection B.X.hom (unitSection B) (unitSection_comp B)).app B.X

lemma origin_eq : unitSection (square B) = unitSection B ≫ axis B := by
  apply pullback.hom_ext
  · have h : unitSection (square B) ≫ pullback.fst B.X.hom B.X.hom =
        unitSection B :=
      congrArg CommaMorphism.left
        (MonObj.one_comp (fst B.X B.X) (X := Over.mk (𝟙 S)))
    simpa only [axis, relativeSection, Category.assoc, pullback.lift_fst,
      Category.comp_id] using h
  · have h : unitSection (square B) ≫ pullback.snd B.X.hom B.X.hom =
        unitSection B :=
      congrArg CommaMorphism.left
        (MonObj.one_comp (snd B.X B.X) (X := Over.mk (𝟙 S)))
    simp only [axis, relativeSection, Category.assoc, pullback.lift_snd]
    rw [← Category.assoc, unitSection_comp, Category.id_comp]
    exact h

/-- Forgetting the axis rigidification and retaining its restriction to the origin. -/
def atOrigin (L : RigidifiedFamily B B.X) : RigidifiedLineBundle (unitSection (square B)) :=
  RigidifiedLineBundle.ofLineBundle ((RigidifiedLineBundle.forget _).obj L)
    ((Langlands.Scheme.Modules.pullbackUnitIso (unitSection B)).symm ≪≫
      (Scheme.Modules.pullback (unitSection B)).mapIso L.obj.rigidification ≪≫
      (Scheme.Modules.pullbackComp (unitSection B) (axis B)).app L.obj.carrier ≪≫
      (Scheme.Modules.pullbackCongr (origin_eq B).symm).app L.obj.carrier)

/-- View an origin-rigidified bundle as a relative family over the identity test. -/
def identityFamily (L : RigidifiedFamily B B.X) :
    RigidifiedFamily (square B) (Over.mk (𝟙 S)) :=
  (RigidifiedLineBundle.pullback (pullback.snd (𝟙 S) (square B).X.hom) (𝟙 S)
    (by
      exact (relativeSection_snd (square B).X.hom (unitSection (square B))
        (unitSection_comp (square B)) (Over.mk (𝟙 S))).trans
          (Category.id_comp _))).obj (atOrigin B L)

lemma pullback_injective_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    Function.Injective (Group.pullback e.hom) := by
  intro q r h
  have h' := congrArg (Group.pullback e.inv) h
  simpa only [← AddMonoidHom.comp_apply, ← Group.pullback_comp, e.inv_hom_id,
    Group.pullback_id, AddMonoidHom.id_apply] using h'

/-- The ordinary class underlying restriction from the identity parameter. -/
lemma identityFamily_class (L : RigidifiedFamily B B.X) (T : Over S) :
    RigidifiedLineBundle.forgetClasses (square B).X.hom
        (unitSection (square B)) (unitSection_comp (square B)) T
      (RigidifiedLineBundle.classifyingMap (square B).X.hom
        (unitSection (square B)) (unitSection_comp (square B)) (identityFamily B L) T
          (Over.mkIdTerminal.from T)) =
      Group.pullback (pullback.snd T.hom (square B).X.hom)
        ((RigidifiedLineBundle.forget _).obj L).classOf := by
  change ((LineBundle.pullback _).obj ((LineBundle.pullback _).obj
    ((RigidifiedLineBundle.forget _).obj L))).classOf = _
  rw [← Group.pullback_lineBundle_classOf, ← Group.pullback_lineBundle_classOf,
    ← AddMonoidHom.comp_apply, ← Group.pullback_comp]
  congr 1
  exact congrArg Group.pullback
    (relativeSpace_map_snd (square B).X.hom (Over.mkIdTerminal.from T))

/-- The parameter-first base change of the carrier, regarded over the original base. -/
abbrev parameter (T : Over S) : Over S :=
  Over.mk (pullback.snd T.hom B.X.hom ≫ B.X.hom)

/-- Its projection back to the original carrier. -/
def parameterMap (T : Over S) : parameter B T ⟶ B.X :=
  Over.homMk (pullback.snd T.hom B.X.hom)

/-- Reassociation identifies the triple product with the family on the self-product. -/
def associate (T : Over S) :
    (relativeSpace B.X.hom).obj (parameter B T) ≅
      (relativeSpace (square B).X.hom).obj T :=
  pullbackAssoc T.hom B.X.hom B.X.hom B.X.hom

lemma associate_snd (T : Over S) :
    (associate B T).hom ≫ pullback.snd T.hom (square B).X.hom =
      (relativeSpace B.X.hom).map (parameterMap B T) := by
  apply pullback.hom_ext
  · change (pullbackAssoc T.hom B.X.hom B.X.hom B.X.hom).hom ≫
        pullback.snd T.hom (pullback.fst B.X.hom B.X.hom ≫ B.X.hom) ≫
          pullback.fst B.X.hom B.X.hom = _
    simp only [pullbackAssoc_hom_snd_fst, relativeSpace, Functor.comp_map,
      Over.forget_map, Over.pullback_map_left, parameterMap, Over.homMk_left,
      pullback.lift_fst]
    rfl
  · change (pullbackAssoc T.hom B.X.hom B.X.hom B.X.hom).hom ≫
        pullback.snd T.hom (pullback.fst B.X.hom B.X.hom ≫ B.X.hom) ≫
          pullback.snd B.X.hom B.X.hom = _
    simp only [pullbackAssoc_hom_snd_snd, relativeSpace, Functor.comp_map,
      Over.forget_map, Over.pullback_map_left, parameterMap, Over.homMk_left,
      pullback.lift_snd]
    rfl

/-- Ordinary classes of an actual classifying pullback. -/
lemma forget_classifying {P T : Over S} (L : RigidifiedFamily B P) (h : T ⟶ P) :
    RigidifiedLineBundle.forgetClasses B.X.hom (unitSection B) (unitSection_comp B) T
      (RigidifiedLineBundle.classifyingMap B.X.hom (unitSection B) (unitSection_comp B)
        L T h) =
      Group.pullback ((relativeSpace B.X.hom).map h)
        ((RigidifiedLineBundle.forget _).obj L).classOf := by
  change ((LineBundle.pullback ((relativeSpace B.X.hom).map h)).obj
    ((RigidifiedLineBundle.forget _).obj L)).classOf = _
  exact (Group.pullback_lineBundle_classOf _ _).symm

/-- Restricting the origin encoding is faithful to the original family on the
parameter-first base change. -/
lemma identityFamily_eq_iff (L M : RigidifiedFamily B B.X) (T : Over S) :
    RigidifiedLineBundle.classifyingMap (square B).X.hom
        (unitSection (square B)) (unitSection_comp (square B)) (identityFamily B L) T
          (Over.mkIdTerminal.from T) =
      RigidifiedLineBundle.classifyingMap (square B).X.hom
        (unitSection (square B)) (unitSection_comp (square B)) (identityFamily B M) T
          (Over.mkIdTerminal.from T) ↔
    RigidifiedLineBundle.classifyingMap B.X.hom (unitSection B) (unitSection_comp B)
        L (parameter B T) (parameterMap B T) =
      RigidifiedLineBundle.classifyingMap B.X.hom (unitSection B) (unitSection_comp B)
        M (parameter B T) (parameterMap B T) := by
  rw [← (RigidifiedLineBundle.forgetClasses_injective (square B).X.hom
    (unitSection (square B)) (unitSection_comp (square B)) T).eq_iff,
    identityFamily_class, identityFamily_class,
    ← (RigidifiedLineBundle.forgetClasses_injective B.X.hom
      (unitSection B) (unitSection_comp B) (parameter B T)).eq_iff,
    forget_classifying, forget_classifying, ← associate_snd, Group.pullback_comp]
  exact (pullback_injective_of_iso (associate B T)).eq_iff.symm

/-- Actual base-change equality is the equality of the maps on `T ×_S B`. -/
lemma baseChange_eq_iff {P : Over S} (f g : B.X ⟶ P) (T : Over S) :
    (Over.pullback T.hom).map f = (Over.pullback T.hom).map g ↔
      parameterMap B T ≫ f = parameterMap B T ≫ g := by
  constructor
  · intro h
    apply Over.OverMorphism.ext
    change pullback.snd T.hom B.X.hom ≫ f.left =
      pullback.snd T.hom B.X.hom ≫ g.left
    have h' := congrArg (fun k => k.left ≫ pullback.fst P.hom T.hom) h
    simp only [Over.pullback_map_left, pullback.lift_fst] at h'
    have h'' := congrArg (fun k => (pullbackSymmetry T.hom B.X.hom).hom ≫ k) h'
    simpa only [← Category.assoc, pullbackSymmetry_hom_comp_fst] using h''
  · intro h
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have h' := congrArg CommaMorphism.left h
      change pullback.snd T.hom B.X.hom ≫ f.left =
        pullback.snd T.hom B.X.hom ≫ g.left at h'
      have h'' := congrArg (fun k => (pullbackSymmetry T.hom B.X.hom).inv ≫ k) h'
      simpa only [Over.pullback_map_left, pullback.lift_fst,
        ← Category.assoc, pullbackSymmetry_inv_comp_snd] using h''
    · simp only [Over.pullback_map_left, pullback.lift_snd]

variable (hB : HasDualScheme B)

/-- Encode a map by its actual rigidified Poincaré pullback. -/
def mapFamily (f : B.X ⟶ dualScheme B hB) : RigidifiedFamily B B.X :=
  (RigidifiedLineBundle.relativePullback B.X.hom (unitSection B)
    (unitSection_comp B) f).obj (poincareFamily B hB)

/-- The ordinary classifying map of a universal Picard-zero family is injective. -/
lemma poincare_classifying_injective (T : Over S) :
    Function.Injective (RigidifiedLineBundle.classifyingMap B.X.hom
      (unitSection B) (unitSection_comp B) (poincareFamily B hB) T) := by
  intro f g h
  apply (picardZeroClassifyingMap_bijective B picardZeroPullback
    (poincareFamily B hB) (poincareFamily_universal B hB) T).injective
  exact Subtype.ext h

/-- Equality of the self-product encodings detects equality of the actual maps
after base change, on every scheme test. -/
lemma encoding_eq_iff (f g : B.X ⟶ dualScheme B hB) (T : Over S) :
    RigidifiedLineBundle.classifyingMap (square B).X.hom
        (unitSection (square B)) (unitSection_comp (square B))
        (identityFamily B (mapFamily B hB f)) T (Over.mkIdTerminal.from T) =
      RigidifiedLineBundle.classifyingMap (square B).X.hom
        (unitSection (square B)) (unitSection_comp (square B))
        (identityFamily B (mapFamily B hB g)) T (Over.mkIdTerminal.from T) ↔
      (Over.pullback T.hom).map f = (Over.pullback T.hom).map g := by
  rw [identityFamily_eq_iff, baseChange_eq_iff]
  change RigidifiedLineBundle.classesPullback B.X.hom (unitSection B)
      (unitSection_comp B) (parameterMap B T)
      (RigidifiedLineBundle.classifyingMap B.X.hom (unitSection B) (unitSection_comp B)
        (poincareFamily B hB) B.X f) =
    RigidifiedLineBundle.classesPullback B.X.hom (unitSection B)
      (unitSection_comp B) (parameterMap B T)
      (RigidifiedLineBundle.classifyingMap B.X.hom (unitSection B) (unitSection_comp B)
        (poincareFamily B hB) B.X g) ↔ _
  rw [← RigidifiedLineBundle.classifyingMap_comp B.X.hom (unitSection B)
    (unitSection_comp B) RigidifiedModule.pullbackCoherence,
    ← RigidifiedLineBundle.classifyingMap_comp B.X.hom (unitSection B)
    (unitSection_comp B) RigidifiedModule.pullbackCoherence]
  exact (poincare_classifying_injective B hB (parameter B T)).eq_iff

/-- A closed subscheme of the base detects equality of a pair of actual maps on
every scheme test. -/
theorem exists_closed_locus (f g : B.X ⟶ dualScheme B hB) :
    ∃ Z : Over S, IsClosedImmersion Z.hom ∧ ∀ T : Over S,
      Nonempty (T ⟶ Z) ↔
        (Over.pullback T.hom).map f = (Over.pullback T.hom).map g := by
  obtain ⟨Z, j, hj, hZ⟩ := rigidifiedClassesEqualizerClosed S (square B)
    (Over.mk (𝟙 S))
    (RigidifiedLineBundle.classOf (square B).X.hom (unitSection (square B))
      (unitSection_comp (square B)) (identityFamily B (mapFamily B hB f)))
    (RigidifiedLineBundle.classOf (square B).X.hom (unitSection (square B))
      (unitSection_comp (square B)) (identityFamily B (mapFamily B hB g)))
  refine ⟨Over.mk j, hj, fun T => ?_⟩
  rw [← encoding_eq_iff B hB f g T]
  change Nonempty (T ⟶ Over.mk j) ↔
    RigidifiedLineBundle.classesPullback (square B).X.hom (unitSection (square B))
        (unitSection_comp (square B)) (Over.mkIdTerminal.from T) _ =
      RigidifiedLineBundle.classesPullback (square B).X.hom (unitSection (square B))
        (unitSection_comp (square B)) (Over.mkIdTerminal.from T) _
  rw [← hZ T (Over.mkIdTerminal.from T)]
  simp only [Over.mkIdTerminal_from_left]
  constructor
  · rintro ⟨k⟩
    exact ⟨k.left, k.w⟩
  · rintro ⟨k, hk⟩
    exact ⟨Over.homMk k hk⟩

/-- The chosen closed equality locus of a pair of actual maps to the chosen dual. -/
def locus (f g : B.X ⟶ dualScheme B hB) : Over S :=
  Classical.choose (exists_closed_locus B hB f g)

instance locus_isClosedImmersion (f g : B.X ⟶ dualScheme B hB) :
    IsClosedImmersion (locus B hB f g).hom :=
  (Classical.choose_spec (exists_closed_locus B hB f g)).1

/-- A test factors through the chosen locus exactly when its actual pullbacks agree. -/
theorem locus_nonempty_iff (f g : B.X ⟶ dualScheme B hB) (T : Over S) :
    Nonempty (T ⟶ locus B hB f g) ↔
      (Over.pullback T.hom).map f = (Over.pullback T.hom).map g :=
  (Classical.choose_spec (exists_closed_locus B hB f g)).2 T

end DualMapEquality
end Langlands.AbelianScheme
