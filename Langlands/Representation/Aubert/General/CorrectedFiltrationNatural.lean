import Langlands.Representation.Aubert.General.CorrectedFiltration
import Langlands.Representation.Aubert.General.Naturality
import Langlands.Representation.Category.Subquotients

/-! Naturality of the corrected support filtration in the ambient representation. -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General.CorrectedFiltration

universe uI uG uV

section Standard

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U : Finset ι → Subgroup G}
  {h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J)}
  {hclosed : ∀ J, IsClosed (U J : Set G)}
  {hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J)}
  {hP : Monotone P} {hU : Antitone U}
variable {T : Subgroup G} [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
variable {Mx : CoxeterMatrix ι} {cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T)}
variable {A B C : SmoothRep.{0, uG, max uG uV} ℂ G}

variable (P M U h hclosed) in
/-- The term map `i_J r_J (φ) : E_J ⟶ E'_J` at the removed roots `s`, `J = S \ s`:
the actual normalized induction--Jacquet functor applied to `φ`. -/
abbrev termMap (φ : A ⟶ B) (s : Finset ι) :
    term P M U h hclosed A s ⟶ term P M U h hclosed B s :=
  (inductionJacquetFunctor.{uG, uV} (h (Finset.univ \ s)) (hclosed (Finset.univ \ s))).map φ

/-- The term map is the term map `Complex.termMap` of the standard complex. -/
theorem hom_termMap (φ : A ⟶ B) (s : Finset ι) :
    SmoothRep.hom (termMap P M U h hclosed φ s) =
      Complex.termMap (StandardComplex.removedFamily P) (StandardComplex.removedFamily M)
        (StandardComplex.removedFamily U) (fun s => h (Finset.univ \ s))
        (fun s => hclosed (Finset.univ \ s)) φ s :=
  rfl

@[simp] theorem termMap_id (s : Finset ι) :
    termMap P M U h hclosed (𝟙 A) s = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

@[simp] theorem termMap_comp (φ : A ⟶ B) (ψ : B ⟶ C) (s : Finset ι) :
    termMap P M U h hclosed (φ ≫ ψ) s =
      termMap P M U h hclosed φ s ≫ termMap P M U h hclosed ψ s :=
  CategoryTheory.Functor.map_comp _ _ _

/-- The term maps commute with the actual transition maps of the complex. -/
theorem transition_termMap (φ : A ⟶ B) {s t : Finset ι} (hst : s ⊆ t) :
    transition P M U h hclosed hδ hP hU A hst ≫ termMap P M U h hclosed φ t =
      termMap P M U h hclosed φ s ≫ transition P M U h hclosed hδ hP hU B hst := by
  apply (SmoothRep.ofHom_hom _).symm.trans
  apply Eq.trans _ (SmoothRep.ofHom_hom _)
  congr 1
  apply Representation.IntertwiningMap.toLinearMap_injective
  exact Complex.termMap_natural (StandardComplex.removedFamily P)
    (StandardComplex.removedFamily M) (StandardComplex.removedFamily U)
    (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
    (fun s => hδ (Finset.univ \ s)) (StandardComplex.removedFamily_antitone hP)
    (StandardComplex.removedFamily_monotone hU) φ hst

/-- The term map acts pointwise on induced functions, so it preserves the support
conditions: it maps the functions in `E_J` supported in `G_{θ_i'}` to functions
in `E'_J` supported in `G_{θ_i'}`. -/
theorem termMap_mem_inductionStep (φ : A ⟶ B) (I s : Finset ι) (i : ℕ)
    {f : term P M U h hclosed A s} (hf : f ∈ inductionStep P M U h hclosed T cs A I s i) :
    SmoothRep.hom (termMap P M U h hclosed φ s) f ∈
      inductionStep P M U h hclosed T cs B I s i := by
  intro g hg
  apply hf g
  intro h0
  apply hg
  have h0' : Induction.eval (StandardComplex.removedFamily P s)
      (inducingRepresentation (h (Finset.univ \ s)) (hclosed (Finset.univ \ s))
        ((jacquetFunctor.{uG, max uG uV} (h (Finset.univ \ s))
          (hclosed (Finset.univ \ s))).obj A)) f g = 0 :=
    h0
  exact (normalizedInductionFunctor_map_eval (h (Finset.univ \ s)) (hclosed (Finset.univ \ s))
    ((jacquetFunctor.{uG, max uG uV} (h (Finset.univ \ s)) (hclosed (Finset.univ \ s))).map φ)
    f g).trans ((congrArg _ h0').trans (map_zero _))

/-- The actual Jacquet map `r_I(i_J r_J φ)` maps each filtration step of `r_I(E_J)`
into the same step of `r_I(E'_J)`. -/
theorem termMap_mem_step (φ : A ⟶ B) (I s : Finset ι) (i : ℕ)
    {x : (jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).obj (term P M U h hclosed A s)}
    (hx : x ∈ (step P M U h hclosed T cs A I s i).toSubmodule) :
    SmoothRep.hom ((jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).map
        (termMap P M U h hclosed φ s)) x ∈
      (step P M U h hclosed T cs B I s i).toSubmodule :=
  jacquetImage_map _ (fun _ hf => termMap_mem_inductionStep φ I s i hf) hx

variable (T cs) in
/-- The restriction of `r_I(i_J r_J φ)` to the filtration steps at `i`, as a morphism
of the actual smooth subrepresentations. -/
def stepMap (φ : A ⟶ B) (I s : Finset ι) (i : ℕ) :
    SmoothRep.subrepresentation
        ((jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).obj (term P M U h hclosed A s))
        (step P M U h hclosed T cs A I s i) ⟶
      SmoothRep.subrepresentation
        ((jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).obj (term P M U h hclosed B s))
        (step P M U h hclosed T cs B I s i) :=
  SmoothRep.ofHom
    { toLinearMap := (SmoothRep.hom ((jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).map
          (termMap P M U h hclosed φ s))).toLinearMap.restrict
        (fun _ hx => termMap_mem_step φ I s i hx)
      isIntertwining' := fun g => LinearMap.ext fun x => Subtype.ext
        (LinearMap.congr_fun ((SmoothRep.hom ((jacquetFunctor.{uG, max uG uV} (h I)
          (hclosed I)).map (termMap P M U h hclosed φ s))).isIntertwining' g) x.1) }

@[simp] theorem stepMap_apply (φ : A ⟶ B) (I s : Finset ι) (i : ℕ)
    (x : SmoothRep.subrepresentation
      ((jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).obj (term P M U h hclosed A s))
      (step P M U h hclosed T cs A I s i)) :
    (SmoothRep.hom (stepMap T cs φ I s i) x).1 =
      SmoothRep.hom ((jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).map
        (termMap P M U h hclosed φ s)) x.1 :=
  rfl

/-- The step map is the restriction of `r_I(i_J r_J φ)` along the inclusions. -/
theorem stepMap_subtype (φ : A ⟶ B) (I s : Finset ι) (i : ℕ) :
    stepMap T cs φ I s i ≫ SmoothRep.subtype _ (step P M U h hclosed T cs B I s i) =
      SmoothRep.subtype _ (step P M U h hclosed T cs A I s i) ≫
        (jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).map
          (termMap P M U h hclosed φ s) := by
  have hh : SmoothRep.hom (stepMap T cs φ I s i ≫
        SmoothRep.subtype _ (step P M U h hclosed T cs B I s i)) =
      SmoothRep.hom (SmoothRep.subtype _ (step P M U h hclosed T cs A I s i) ≫
        (jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).map
          (termMap P M U h hclosed φ s)) := by
    ext x
    rfl
  simpa only [SmoothRep.ofHom_hom] using congrArg SmoothRep.ofHom hh

end Standard

end Langlands.Aubert.General.CorrectedFiltration
