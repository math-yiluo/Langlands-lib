import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartTerminal
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Topology.Sheaves.Presheaf

/-! # Actual compatible rational algebra sections on topological opens -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory TopologicalSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}

namespace OpenSections

/-- Actual rational charts whose entire locus lies in the prescribed set. -/
def ChartIn (U : Set (BanachSpectrum A)) :=
  {d : RationalChart K A // d.locus ⊆ U}

/-- Families of actual quotient-algebra elements compatible under all actual
bounded restrictions between charts contained in the set. -/
def compatibleAlgebra (U : Set (BanachSpectrum A)) :
    Subalgebra K (∀ d : ChartIn U, d.val.algebra) where
  carrier := {s | ∀ (d e : ChartIn U) (f : d.val ⟶ e.val),
    f.restriction (s e) = s d}
  zero_mem' := by
    intro d e f
    exact map_zero f.restriction.toAlgHom
  one_mem' := by
    intro d e f
    exact map_one f.restriction.toAlgHom
  add_mem' := by
    intro s t hs ht d e f
    exact (map_add f.restriction.toAlgHom _ _).trans (congrArg₂ (· + ·) (hs d e f) (ht d e f))
  mul_mem' := by
    intro s t hs ht d e f
    exact (map_mul f.restriction.toAlgHom _ _).trans (congrArg₂ (· * ·) (hs d e f) (ht d e f))
  algebraMap_mem' := by
    intro a d e f
    exact f.restriction.toAlgHom.commutes a

/-- The actual K-algebra of compatible rational section families. -/
abbrev Sections (U : Set (BanachSpectrum A)) := ↥(compatibleAlgebra U)

@[ext]
theorem ext {U : Set (BanachSpectrum A)} {s t : Sections U}
    (h : ∀ d : ChartIn U, s.val d = t.val d) : s = t :=
  Subtype.ext (funext h)

/-- Evaluation retains the actual quotient algebra of a chosen contained chart. -/
def evaluation (U : Set (BanachSpectrum A)) (d : ChartIn U) :
    Sections U →ₐ[K] d.val.algebra :=
  (Pi.evalAlgHom K (fun e : ChartIn U => e.val.algebra) d).comp
    (compatibleAlgebra U).val

@[simp]
theorem evaluation_apply (U : Set (BanachSpectrum A)) (d : ChartIn U)
    (s : Sections U) : evaluation U d s = s.val d := rfl

theorem compatible {U : Set (BanachSpectrum A)} (s : Sections U)
    (d e : ChartIn U) (f : d.val ⟶ e.val) :
    f.restriction (s.val e) = s.val d :=
  s.property d e f

/-- Restriction forgets the components not contained in the smaller set. -/
def restriction {U V : Set (BanachSpectrum A)} (h : U ⊆ V) :
    Sections V →ₐ[K] Sections U where
  toFun s := ⟨fun d => s.val ⟨d.val, d.property.trans h⟩,
    fun d e f => s.property ⟨d.val, d.property.trans h⟩
      ⟨e.val, e.property.trans h⟩ f⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem restriction_apply {U V : Set (BanachSpectrum A)} (h : U ⊆ V)
    (s : Sections V) (d : ChartIn U) :
    (restriction h s).val d = s.val ⟨d.val, d.property.trans h⟩ := rfl

@[simp]
theorem restriction_id (U : Set (BanachSpectrum A)) :
    restriction (Set.Subset.refl U) = AlgHom.id K (Sections U) := by
  ext s d
  rfl

theorem restriction_comp {U V W : Set (BanachSpectrum A)}
    (h : U ⊆ V) (k : V ⊆ W) :
    (restriction h).comp (restriction k) = restriction (h.trans k) := by
  ext s d
  rfl

/-- An element of the original algebra gives its actual structural image
in every contained rational quotient. -/
def fromBase (U : Set (BanachSpectrum A)) : A →ₐ[K] Sections U where
  toFun a := ⟨fun d => d.val.baseMap a, fun d e f =>
    congrArg (fun g : BoundedAlgHom K A d.val.algebra => g a) f.comp_baseMap⟩
  map_zero' := by
    apply ext
    intro d
    exact map_zero d.val.baseMap.toAlgHom
  map_one' := by
    apply ext
    intro d
    exact map_one d.val.baseMap.toAlgHom
  map_add' a b := by
    apply ext
    intro d
    exact map_add d.val.baseMap.toAlgHom a b
  map_mul' a b := by
    apply ext
    intro d
    exact map_mul d.val.baseMap.toAlgHom a b
  commutes' a := by
    apply ext
    intro d
    exact d.val.baseMap.toAlgHom.commutes a

@[simp]
theorem fromBase_apply (U : Set (BanachSpectrum A)) (a : A) (d : ChartIn U) :
    (fromBase U a).val d = d.val.baseMap a := rfl

@[simp]
theorem restriction_fromBase {U V : Set (BanachSpectrum A)} (h : U ⊆ V) (a : A) :
    restriction h (fromBase V a) = fromBase U a := rfl

variable [CompleteSpace K]

/-- On a rational locus, restrict the actual chart element to every contained
chart using the proved full rational-domain representation. -/
def fromChart (d : RationalChart K A) : d.algebra →ₐ[K] Sections d.locus where
  toFun a := ⟨fun e => (restrictionOfSubset e.val d e.property).restriction a, by
    intro e g f
    exact congrArg (fun h : e.val ⟶ d => h.restriction a)
      (@Subsingleton.elim (Restriction e.val d) inferInstance
        (f ≫ restrictionOfSubset g.val d g.property)
        (restrictionOfSubset e.val d e.property))⟩
  map_zero' := by
    apply ext
    intro e
    exact map_zero (restrictionOfSubset e.val d e.property).restriction.toAlgHom
  map_one' := by
    apply ext
    intro e
    exact map_one (restrictionOfSubset e.val d e.property).restriction.toAlgHom
  map_add' a b := by
    apply ext
    intro e
    exact map_add (restrictionOfSubset e.val d e.property).restriction.toAlgHom a b
  map_mul' a b := by
    apply ext
    intro e
    exact map_mul (restrictionOfSubset e.val d e.property).restriction.toAlgHom a b
  commutes' a := by
    apply ext
    intro e
    exact (restrictionOfSubset e.val d e.property).restriction.toAlgHom.commutes a

/-- Evaluation at the chart and actual bounded restrictions are inverse
algebra maps on its rational locus. -/
def chartEquiv (d : RationalChart K A) : d.algebra ≃ₐ[K] Sections d.locus :=
  AlgEquiv.ofAlgHom (fromChart d) (evaluation d.locus ⟨d, Set.Subset.refl _⟩)
    (by
      ext s e
      exact s.property e ⟨d, Set.Subset.refl _⟩
        (restrictionOfSubset e.val d e.property))
    (by
      ext a
      change (restrictionOfSubset d d (Set.Subset.refl _)).restriction a = a
      rw [restrictionOfSubset_self]
      rfl)

@[simp]
theorem chartEquiv_apply (d : RationalChart K A) (a : d.algebra)
    (e : ChartIn d.locus) :
    (chartEquiv d a).val e = (restrictionOfSubset e.val d e.property).restriction a := rfl

@[simp]
theorem chartEquiv_symm_apply (d : RationalChart K A) (s : Sections d.locus) :
    (chartEquiv d).symm s = s.val ⟨d, Set.Subset.refl _⟩ := rfl

/-- Global compatible families recover the original affinoid algebra,
through the actual whole-chart retraction. -/
def globalEquiv : A ≃ₐ[K] Sections (Set.univ : Set (BanachSpectrum A)) :=
  AlgEquiv.ofAlgHom (fromBase Set.univ)
    ((wholeRetraction K A).toAlgHom.comp
      (evaluation Set.univ ⟨whole K A, Set.subset_univ _⟩))
    (by
      ext s d
      exact s.property d ⟨whole K A, Set.subset_univ _⟩ (toWhole K A d.val))
    (by
      ext a
      exact wholeRetraction_baseMap K A a)

@[simp]
theorem globalEquiv_apply (a : A) (d : ChartIn (Set.univ : Set (BanachSpectrum A))) :
    (globalEquiv a).val d = d.val.baseMap a := rfl

@[simp]
theorem globalEquiv_symm_apply (s : Sections (Set.univ : Set (BanachSpectrum A))) :
    globalEquiv.symm s = wholeRetraction K A
      (s.val ⟨whole K A, Set.subset_univ _⟩) := rfl

end OpenSections

variable (K A)

/-- The presheaf of actual compatible rational algebra families on the
topological opens of the actual affinoid spectrum. -/
def openAlgebraPresheaf :
    (Opens (BanachSpectrum A))ᵒᵖ ⥤ CommAlgCat K where
  obj U := CommAlgCat.of K (OpenSections.Sections (U.unop : Set (BanachSpectrum A)))
  map f := CommAlgCat.ofHom (OpenSections.restriction f.unop.le)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem openAlgebraPresheaf_map_apply {U V : Opens (BanachSpectrum A)}
    (f : U ⟶ V) (s : OpenSections.Sections (V : Set (BanachSpectrum A)))
    (d : OpenSections.ChartIn (U : Set (BanachSpectrum A))) :
    ((openAlgebraPresheaf K A).map f.op s).val d =
      s.val ⟨d.val, d.property.trans f.le⟩ := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
