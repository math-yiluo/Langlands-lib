import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.Topology.Algebra.Group.Units

/-! # Arithmetic functoriality at infinite places -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField
open scoped NumberField

universe u v w

variable {K : Type u} {L : Type v} {M : Type w}
  [Field K] [Field L] [Field M]

private instance : T2Space (InfiniteAdeleRing K) :=
  inferInstanceAs (T2Space ((p : InfinitePlace K) → p.Completion))

/-- Pullback of infinite places along an actual field isomorphism. -/
def infinitePlaceEquiv (e : K ≃+* L) : InfinitePlace L ≃ InfinitePlace K where
  toFun p := p.comap e.toRingHom
  invFun p := p.comap e.symm.toRingHom
  left_inv p := by ext x; simp [InfinitePlace.comap_apply]
  right_inv p := by ext x; simp [InfinitePlace.comap_apply]

@[simp] theorem infinitePlaceEquiv_apply (e : K ≃+* L) (p : InfinitePlace L) (x : K) :
    infinitePlaceEquiv e p x = p (e x) := rfl

@[simp] theorem infinitePlaceEquiv_refl :
    infinitePlaceEquiv (RingEquiv.refl K) = Equiv.refl (InfinitePlace K) := by
  ext p x
  rfl

theorem infinitePlaceEquiv_trans (e : K ≃+* L) (f : L ≃+* M) :
    infinitePlaceEquiv (e.trans f) = (infinitePlaceEquiv f).trans (infinitePlaceEquiv e) := by
  ext p x
  rfl

private theorem withAbsMap_isometry (f : K →+* L) (p : InfinitePlace L) :
    Isometry (WithAbs.map (p.comap f).1 p.1 f) := by
  rw [AddMonoidHomClass.isometry_iff_norm]
  intro x
  rfl

/-- Extension of a field embedding to the completions at a place and its pullback. -/
def infiniteCompletionMap (f : K →+* L) (p : InfinitePlace L) :
    (p.comap f).Completion →+* p.Completion :=
  (InfinitePlace.Completion.equiv p).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
      (WithAbs.map (p.comap f).1 p.1 f) (withAbsMap_isometry f p).continuous).comp
      (InfinitePlace.Completion.equiv (p.comap f)).toRingHom)

theorem continuous_infiniteCompletionMap (f : K →+* L) (p : InfinitePlace L) :
    Continuous (infiniteCompletionMap f p) :=
  (InfinitePlace.Completion.continuous_ofCompletion p).comp
    (UniformSpace.Completion.continuous_map.comp
      (InfinitePlace.Completion.continuous_toCompletion (p.comap f)))

@[simp] theorem infiniteCompletionMap_coe (f : K →+* L) (p : InfinitePlace L) (x : K) :
    infiniteCompletionMap f p (algebraMap K (p.comap f).Completion x) =
      algebraMap L p.Completion (f x) := by
  apply (InfinitePlace.Completion.equiv p).injective
  change UniformSpace.Completion.mapRingHom (WithAbs.map (p.comap f).1 p.1 f)
    (withAbsMap_isometry f p).continuous
    (↑(WithAbs.toAbs (p.comap f).1 x)) = _
  rw [UniformSpace.Completion.mapRingHom_coe]
  rfl

private def withAbsRingEquiv (e : K ≃+* L) (p : InfinitePlace L) :
    WithAbs (p.comap e.toRingHom).1 ≃+* WithAbs p.1 :=
  (WithAbs.equiv _).trans (e.trans (WithAbs.equiv _).symm)

private def withAbsIsometryEquiv (e : K ≃+* L) (p : InfinitePlace L) :
    WithAbs (p.comap e.toRingHom).1 ≃ᵢ WithAbs p.1 where
  __ := (withAbsRingEquiv e p).toEquiv
  isometry_toFun := withAbsMap_isometry e.toRingHom p

/-- An actual field isomorphism extends to the corresponding completed fields. -/
def infiniteCompletionEquiv (e : K ≃+* L) (p : InfinitePlace L) :
    (p.comap e.toRingHom).Completion ≃+* p.Completion :=
  (InfinitePlace.Completion.equiv _).trans
    ((UniformSpace.Completion.mapRingEquiv (withAbsRingEquiv e p)
      (withAbsIsometryEquiv e p).continuous (withAbsIsometryEquiv e p).symm.continuous).trans
      (InfinitePlace.Completion.equiv p).symm)

@[simp] theorem infiniteCompletionEquiv_apply (e : K ≃+* L) (p : InfinitePlace L)
    (x : (p.comap e.toRingHom).Completion) :
    infiniteCompletionEquiv e p x = infiniteCompletionMap e.toRingHom p x := rfl

/-- The same completed-field isomorphism, with its isometry bundled. -/
def infiniteCompletionIsometryEquiv (e : K ≃+* L) (p : InfinitePlace L) :
    (p.comap e.toRingHom).Completion ≃ᵢ p.Completion where
  __ := (infiniteCompletionEquiv e p).toEquiv
  isometry_toFun :=
    (InfinitePlace.Completion.isometryEquivCompletion p).symm.isometry.comp
      ((UniformSpace.Completion.isometry_mapRingHom (withAbsMap_isometry e.toRingHom p)).comp
        (InfinitePlace.Completion.isometry_toCompletion _))

/-- Both continuities of completed-field transport. -/
def infiniteCompletionHomeomorph (e : K ≃+* L) (p : InfinitePlace L) :
    (p.comap e.toRingHom).Completion ≃ₜ p.Completion :=
  (infiniteCompletionIsometryEquiv e p).toHomeomorph

/-- Coordinate transport on the genuine infinite adele ring. -/
def infiniteAdeleMap (f : K →+* L) : InfiniteAdeleRing K →+* InfiniteAdeleRing L where
  toFun x p := infiniteCompletionMap f p (x (p.comap f))
  map_one' := by funext p; exact map_one _
  map_zero' := by funext p; exact map_zero _
  map_add' x y := by funext p; exact map_add _ _ _
  map_mul' x y := by funext p; exact map_mul _ _ _

@[simp] theorem infiniteAdeleMap_apply (f : K →+* L) (x : InfiniteAdeleRing K)
    (p : InfinitePlace L) :
    infiniteAdeleMap f x p = infiniteCompletionMap f p (x (p.comap f)) := rfl

theorem continuous_infiniteAdeleMap (f : K →+* L) :
    Continuous (infiniteAdeleMap f) :=
  continuous_pi fun p => (continuous_infiniteCompletionMap f p).comp
    (continuous_apply (p.comap f))

@[simp] theorem infiniteAdeleMap_diagonal (f : K →+* L) (x : K) :
    infiniteAdeleMap f (algebraMap K (InfiniteAdeleRing K) x) =
      algebraMap L (InfiniteAdeleRing L) (f x) := by
  funext p
  exact infiniteCompletionMap_coe f p x

variable [NumberField K]

@[simp] theorem infiniteAdeleMap_id :
    infiniteAdeleMap (RingHom.id K) = RingHom.id (InfiniteAdeleRing K) := by
  apply DFunLike.ext'
  apply (InfiniteAdeleRing.denseRange_algebraMap K).equalizer
    (continuous_infiniteAdeleMap _) continuous_id
  funext x
  exact infiniteAdeleMap_diagonal _ x

theorem infiniteAdeleMap_comp (g : L →+* M) (f : K →+* L) :
    infiniteAdeleMap (g.comp f) = (infiniteAdeleMap g).comp (infiniteAdeleMap f) := by
  apply DFunLike.ext'
  apply (InfiniteAdeleRing.denseRange_algebraMap K).equalizer
    (continuous_infiniteAdeleMap _)
    ((continuous_infiniteAdeleMap g).comp (continuous_infiniteAdeleMap f))
  funext x
  simp

/-- The ring isomorphism induced by a number-field isomorphism. -/
def infiniteAdeleEquiv [NumberField L] (e : K ≃+* L) :
    InfiniteAdeleRing K ≃+* InfiniteAdeleRing L where
  __ := infiniteAdeleMap e.toRingHom
  invFun := infiniteAdeleMap e.symm.toRingHom
  left_inv x := by
    have h := infiniteAdeleMap_comp e.symm.toRingHom e.toRingHom
    have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id K := by ext; simp
    rw [he, infiniteAdeleMap_id] at h
    exact (RingHom.congr_fun h x).symm
  right_inv x := by
    have h := infiniteAdeleMap_comp e.toRingHom e.symm.toRingHom
    have he : e.toRingHom.comp e.symm.toRingHom = RingHom.id L := by ext; simp
    rw [he, infiniteAdeleMap_id] at h
    exact (RingHom.congr_fun h x).symm

theorem continuous_infiniteAdeleEquiv [NumberField L] (e : K ≃+* L) :
    Continuous (infiniteAdeleEquiv e) := continuous_infiniteAdeleMap _

theorem continuous_infiniteAdeleEquiv_symm [NumberField L] (e : K ≃+* L) :
    Continuous (infiniteAdeleEquiv e).symm := continuous_infiniteAdeleMap _

/-- The same arithmetic isomorphism with both continuities bundled. -/
def infiniteAdeleHomeomorph [NumberField L] (e : K ≃+* L) :
    InfiniteAdeleRing K ≃ₜ InfiniteAdeleRing L where
  __ := (infiniteAdeleEquiv e).toEquiv
  continuous_toFun := continuous_infiniteAdeleEquiv e
  continuous_invFun := continuous_infiniteAdeleEquiv_symm e

@[simp] theorem infiniteAdeleEquiv_diagonal [NumberField L] (e : K ≃+* L) (x : K) :
    infiniteAdeleEquiv e (algebraMap K (InfiniteAdeleRing K) x) =
      algebraMap L (InfiniteAdeleRing L) (e x) := infiniteAdeleMap_diagonal _ _

@[simp] theorem infiniteAdeleEquiv_refl :
    infiniteAdeleEquiv (RingEquiv.refl K) = RingEquiv.refl (InfiniteAdeleRing K) := by
  ext x
  exact RingHom.congr_fun infiniteAdeleMap_id x

theorem infiniteAdeleEquiv_trans [NumberField L] [NumberField M]
    (e : K ≃+* L) (f : L ≃+* M) :
    infiniteAdeleEquiv (e.trans f) = (infiniteAdeleEquiv e).trans (infiniteAdeleEquiv f) := by
  ext x
  exact RingHom.congr_fun (infiniteAdeleMap_comp f.toRingHom e.toRingHom) x

/-- The actual automorphism group acts by arithmetic ring automorphisms. -/
def infiniteAdeleAut : (K ≃ₐ[ℚ] K) →* (InfiniteAdeleRing K ≃+* InfiniteAdeleRing K) where
  toFun σ := infiniteAdeleEquiv σ.toRingEquiv
  map_one' := infiniteAdeleEquiv_refl
  map_mul' σ τ := by
    ext x
    exact RingHom.congr_fun (infiniteAdeleMap_comp σ.toRingHom τ.toRingHom) x

theorem continuous_infiniteAdeleAut (σ : K ≃ₐ[ℚ] K) :
    Continuous (infiniteAdeleAut σ) := continuous_infiniteAdeleEquiv _

variable [IsCMField K]

/-- CM conjugation on infinite adeles is induced by Mathlib's field conjugation. -/
def infiniteComplexConj : InfiniteAdeleRing K ≃+* InfiniteAdeleRing K :=
  infiniteAdeleEquiv (IsCMField.complexConj K).toRingEquiv

theorem continuous_infiniteComplexConj :
    Continuous (infiniteComplexConj (K := K)) := continuous_infiniteAdeleEquiv _

@[simp] theorem infiniteComplexConj_diagonal (x : K) :
    infiniteComplexConj (algebraMap K (InfiniteAdeleRing K) x) =
      algebraMap K (InfiniteAdeleRing K) (IsCMField.complexConj K x) :=
  infiniteAdeleEquiv_diagonal _ _

@[simp] theorem infiniteComplexConj_involutive :
    Function.Involutive (infiniteComplexConj (K := K)) := by
  have h : (IsCMField.complexConj K).toRingEquiv.trans
      (IsCMField.complexConj K).toRingEquiv = RingEquiv.refl K := by
    ext x
    exact IsCMField.complexConj_apply_apply K x
  intro x
  have hh := infiniteAdeleEquiv_trans (IsCMField.complexConj K).toRingEquiv
    (IsCMField.complexConj K).toRingEquiv
  rw [h, infiniteAdeleEquiv_refl] at hh
  exact (RingEquiv.congr_fun hh x).symm

@[simp] theorem infinitePlaceEquiv_complexConj (p : InfinitePlace K) :
    infinitePlaceEquiv (IsCMField.complexConj K).toRingEquiv p = p := by
  ext x
  exact IsCMField.infinitePlace_complexConj K p x

theorem infiniteComplexConj_coordinate (p : InfinitePlace K) (x : InfiniteAdeleRing K) :
    InfinitePlace.Completion.extensionEmbedding p (infiniteComplexConj x p) =
      star (InfinitePlace.Completion.extensionEmbedding p (x p)) := by
  have h := (InfiniteAdeleRing.denseRange_algebraMap K).equalizer
    ((InfinitePlace.Completion.isometry_extensionEmbedding p).continuous.comp
      ((continuous_apply p).comp continuous_infiniteComplexConj))
    (continuous_star.comp ((InfinitePlace.Completion.isometry_extensionEmbedding p).continuous.comp
      (continuous_apply p))) (by
        funext a
        change InfinitePlace.Completion.extensionEmbedding p
          (infiniteComplexConj (algebraMap K (InfiniteAdeleRing K) a) p) =
          star (InfinitePlace.Completion.extensionEmbedding p
            (algebraMap K (InfiniteAdeleRing K) a p))
        rw [infiniteComplexConj_diagonal]
        change InfinitePlace.Completion.extensionEmbedding p
          (↑(WithAbs.toAbs p.1 (IsCMField.complexConj K a))) =
          star (InfinitePlace.Completion.extensionEmbedding p (↑(WithAbs.toAbs p.1 a)))
        simp only [InfinitePlace.Completion.extensionEmbedding_coe]
        exact (IsCMField.isConj_complexConj K p.embedding).eq a)
  exact congrFun h x

end Langlands.Global.AdelicFunctoriality
