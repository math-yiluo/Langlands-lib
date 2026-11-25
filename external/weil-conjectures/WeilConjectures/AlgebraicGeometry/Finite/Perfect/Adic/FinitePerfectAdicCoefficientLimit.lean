/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicComplexRoos
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # The ordinary limit of the actual coefficient module tower

Source: Stacks Project, Tag 09C6, the coefficient case of the finite-projective calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The actual finite-coefficient module diagram, including its specified transitions.
Source: Stacks Tag 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-coefficient-limit). -/
def finitePerfectAdicCoefficientDiagram (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) : ℕᵒᵖ ⥤ CompletedAdicModules X d :=
  Functor.ofOpSequence (completedAdicFiniteModuleStep X d)

private theorem coefficientStep_apply (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : (completedAdicFiniteRing X d (n + 1)).obj.obj U) :
    (completedAdicFiniteModuleStep X d n).val.app U x =
      (completedAdicFiniteStep X d n).hom.app U x :=
  (completedAdicFiniteModuleStep_exists X d n).exists.choose_spec U x

/-- The limit projections, viewed as linear maps of coefficient modules.
Source: Stacks Tag 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-coefficient-limit). -/
def finitePerfectAdicCoefficientProjection (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    SheafOfModules.unit (completedAdicRing X d) ⟶ completedAdicFiniteModule X d n where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (SheafOfModules.unit (completedAdicRing X d)).val.obj U)
        (Y := (completedAdicFiniteModule X d n).val.obj U)
        { toFun := (completedAdicProjection X d n).hom.app U
          map_add' := map_add _
          map_smul' := by
            intro r x
            change (completedAdicRing X d).obj.obj U at x
            change (completedAdicProjection X d n).hom.app U (r * x) =
              (completedAdicProjection X d n).hom.app U r *
                (completedAdicProjection X d n).hom.app U x
            exact map_mul _ _ _ }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom
          ((completedAdicProjection X d n).hom.naturality f) x }

/-- The completed coefficient unit supplies a cone of actual quotient projections.
Source: Stacks Tag 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-coefficient-limit). -/
def finitePerfectAdicCoefficientCone (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) : Cone (finitePerfectAdicCoefficientDiagram X d) where
  pt := SheafOfModules.unit (completedAdicRing X d)
  π := NatTrans.ofOpSequence (finitePerfectAdicCoefficientProjection X d) (by
    intro n
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (completedAdicRing X d).obj.obj U at x
    simp only [Functor.const_obj_map,
      finitePerfectAdicCoefficientDiagram, Functor.ofOpSequence_map_homOfLE_succ]
    change (completedAdicProjection X d n).hom.app U x =
      (completedAdicFiniteModuleStep X d n).val.app U
        ((completedAdicProjection X d (n + 1)).hom.app U x)
    rw [coefficientStep_apply]
    have h : completedAdicProjection X d (n + 1) ≫
        completedAdicFiniteStep X d n = completedAdicProjection X d n := by
      simpa only [completedAdicProjection, completedAdicRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ] using
        limit.w (completedAdicRingSystem X d) (homOfLE n.le_succ).op
    exact (congrArg (fun f : completedAdicRing X d ⟶
      completedAdicFiniteRing X d n ↦ (f.hom.app U).hom x) h).symm)

/-- The completed coefficient unit is the limit of the actual quotient module diagram.

Source: Stacks Project, Tag 09C6, the coefficient case of the displayed limit calculation.
(blueprint: lem-weil-pbc-finite-perfect-adic-coefficient-limit).

Proof: forget to module presheaves and evaluate on each site object. Forget the scalar
module structure to additive groups. The resulting diagram and cone are the additive
groups of the ring diagram and its defining limit cone, with exactly the same
projections. These forgetful and evaluation functors preserve limits; scalar
restriction and evaluation reflect the limit assertions. Thus the coefficient cone
is a limit in module sheaves. This includes zero rings and empty site objects. -/
theorem finitePerfectAdicCoefficient_isLimit (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) : Nonempty (IsLimit (finitePerfectAdicCoefficientCone X d)) := by
  classical
  refine ⟨?_⟩
  apply isLimitOfReflects (SheafOfModules.forget (completedAdicRing X d))
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro U
  apply isLimitOfReflects
    (forget₂ (ModuleCat.{t + 1} ((completedAdicRing X d).obj.obj U)) AddCommGrpCat)
  let F := finitePerfectAdicCoefficientDiagram X d ⋙
    SheafOfModules.evaluation (completedAdicRing X d) U ⋙
      forget₂ _ AddCommGrpCat
  let E := sheafToPresheaf (ProEt.topology X) RingCat.{t + 1} ⋙
    (CategoryTheory.evaluation X.ProEtᵒᵖ RingCat.{t + 1}).obj U ⋙
      forget₂ RingCat AddCommGrpCat
  let G := completedAdicRingSystem X d ⋙ E
  let α : F ⟶ G := NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
    intro n
    ext x
    simp only [F, G, E, finitePerfectAdicCoefficientDiagram, completedAdicRingSystem,
      Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ,
      Category.id_comp, Category.comp_id]
    exact coefficientStep_apply X d n U x)
  have (n : ℕᵒᵖ) : IsIso (α.app n) := inferInstanceAs (IsIso (𝟙 _))
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let c := (forget₂ (ModuleCat.{t + 1} ((completedAdicRing X d).obj.obj U))
    AddCommGrpCat).mapCone
      ((PresheafOfModules.evaluation (completedAdicRing X d).obj U).mapCone
        ((SheafOfModules.forget (completedAdicRing X d)).mapCone
          (finitePerfectAdicCoefficientCone X d)))
  apply (IsLimit.postcomposeHomEquiv (asIso α) c).toFun
  exact (isLimitOfPreserves E (limit.isLimit (completedAdicRingSystem X d))).ofIsoLimit
    (Cone.ext (Iso.refl _) (by
      intro n
      ext x
      rfl))

/-- The actual consecutive coefficient module map is epimorphic.

Source: Stacks Tag 09C6 and Modules on Sites, Tag 03DA.
(blueprint: lem-weil-pbc-finite-perfect-adic-coefficient-limit).
Proof: choose a set section of the surjective quotient map. Since both finite rings
are discrete, the section is continuous; postcomposition lifts each continuous
coefficient section. Sheafification preserves local surjectivity. The normalized
module map has the same functions on sections, so its underlying additive sheaf map
is locally surjective and hence epi. Faithful forgetting reflects epimorphisms. -/
theorem finitePerfectAdicCoefficientStep_epi (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) : Epi (completedAdicFiniteModuleStep X d n) := by
  classical
  let J := ProEt.topology X
  let q : completedAdicQuotient d (n + 1) →+* completedAdicQuotient d n :=
    RingHom.ulift (adicQuotientMap d.ideal (n + 2) (n + 1) (Nat.le_succ _))
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.Quotient.factor_surjective
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) y.down
    exact ⟨ULift.up x, congrArg ULift.up hx⟩
  choose σ hσ using hq
  have hp : Presheaf.IsLocallySurjective J (completedAdicFinitePresheafStep X d n) := by
    apply Presheaf.isLocallySurjective_of_surjective
    intro U s
    change C(ConnectedComponents U.unop.left, completedAdicQuotient d n) at s
    let τ : C(completedAdicQuotient d n, completedAdicQuotient d (n + 1)) :=
      ⟨σ, continuous_of_discreteTopology⟩
    refine ⟨τ.comp s, ?_⟩
    change (⟨q, continuous_of_discreteTopology⟩ :
      C(completedAdicQuotient d (n + 1), completedAdicQuotient d n)).comp (τ.comp s) = s
    apply ContinuousMap.ext
    intro x
    exact hσ (s x)
  have hr : Sheaf.IsLocallySurjective (completedAdicFiniteStep X d n) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J
      (completedAdicFinitePresheafStep X d n)).2 hp
  let F := SheafOfModules.toSheaf (completedAdicRing X d)
  let g := F.map (completedAdicFiniteModuleStep X d n)
  have hg : Sheaf.IsLocallySurjective g := by
    constructor
    intro U s
    have heq : Presheaf.imageSieve g.hom s =
        Presheaf.imageSieve (completedAdicFiniteStep X d n).hom s := by
      ext V f
      change (∃ x, g.hom.app (op V) x = _) ↔
        ∃ x, (completedAdicFiniteStep X d n).hom.app (op V) x = _
      simp only [show ∀ x, g.hom.app (op V) x =
        (completedAdicFiniteStep X d n).hom.app (op V) x from
          coefficientStep_apply X d n (op V)]
      rfl
    rw [heq]
    exact Presheaf.imageSieve_mem J (completedAdicFiniteStep X d n).hom s
  have : Epi g := Sheaf.epi_of_isLocallySurjective g
  exact F.epi_of_epi_map inferInstance

/-- Compatible retracts of the actual finite-free coefficient diagram have their
specified retract cone as a limit, and its degree-zero localization as a Roos limit.

Source: Stacks Project, Tag 09C6, the finite-projective summand step.
(blueprint: lem-weil-pbc-finite-perfect-adic-coefficient-limit).

Proof: lift a cone into the finite-free limit after the inclusion, then project to
its retract. The two compatibility equations and the splitting prove factorization.
For uniqueness, include into the free limit and use its uniqueness, then project.
Each transition in the retract diagram is epimorphic: its composite with the split
epimorphism from the free term is the free transition followed by a split epimorphism.
Finally apply the epimorphic-complex Roos theorem to the degree-zero complex tower. -/
theorem finitePerfectAdicRetract_roos (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (r : ℕ)
    (B : ℕᵒᵖ ⥤ CompletedAdicModules X d)
    (ι : B ⟶ finitePerfectAdicCoefficientDiagram X d ⋙
      Functor.const (Discrete (Fin r)) ⋙ lim)
    (π : finitePerfectAdicCoefficientDiagram X d ⋙
      Functor.const (Discrete (Fin r)) ⋙ lim ⟶ B)
    (hιπ : ι ≫ π = 𝟙 B) (c : Cone B)
    (i : c.pt ⟶ (lim (J := Discrete (Fin r))).obj
      ((Functor.const (Discrete (Fin r))).obj (SheafOfModules.unit (completedAdicRing X d))))
    (p : (lim (J := Discrete (Fin r))).obj
      ((Functor.const (Discrete (Fin r))).obj (SheafOfModules.unit (completedAdicRing X d)))
        ⟶ c.pt)
    (hip : i ≫ p = 𝟙 c.pt)
    (hi : ∀ n : ℕᵒᵖ, i ≫
      (Functor.const (Discrete (Fin r)) ⋙ lim).map
        ((finitePerfectAdicCoefficientCone X d).π.app n) = c.π.app n ≫ ι.app n)
    (hp : ∀ n : ℕᵒᵖ, p ≫ c.π.app n =
      (Functor.const (Discrete (Fin r)) ⋙ lim).map
        ((finitePerfectAdicCoefficientCone X d).π.app n) ≫ π.app n) :
    let S := HomologicalComplex.single (CompletedAdicModules X d) (.up ℤ) 0
    let T := B ⋙ S
    Nonempty (IsLimit c) ∧ (∀ n : ℕ, Epi (B.map (homOfLE n.le_succ).op)) ∧
    HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (T.obj (op n))) ∧
    ∀ [HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (T.obj (op n)))],
      IsDerivedLimit (K := fun n : ℕ ↦ DerivedCategory.Q.obj (T.obj (op n)))
        (fun n : ℕ ↦ DerivedCategory.Q.map (T.map (homOfLE n.le_succ).op))
        (DerivedCategory.Q.obj (S.obj c.pt)) := by
  classical
  let : HasLimitsOfShape (Discrete (Fin r)) (CompletedAdicModules X d) := inferInstance
  have : HasFiniteBiproducts (CompletedAdicModules X d) := Abelian.hasFiniteBiproducts
  let F : CompletedAdicModules X d ⥤ CompletedAdicModules X d :=
    Functor.const (Discrete (Fin r)) ⋙ lim
  let a := F.mapCone (finitePerfectAdicCoefficientCone X d)
  obtain ⟨hcoef⟩ := finitePerfectAdicCoefficient_isLimit X d
  let ha : IsLimit a := isLimitOfPreserves F hcoef
  let hc : IsLimit c :=
    { lift := fun s ↦ ha.lift { pt := s.pt, π := s.π ≫ ι } ≫ p
      fac := by
        intro s n
        rw [Category.assoc, hp n, ← Category.assoc]
        change (ha.lift { pt := s.pt, π := s.π ≫ ι } ≫ a.π.app n) ≫
          π.app n = s.π.app n
        rw [ha.fac]
        change (s.π.app n ≫ ι.app n) ≫ π.app n = s.π.app n
        rw [Category.assoc, show ι.app n ≫ π.app n = 𝟙 _ by
          simpa only [NatTrans.comp_app, NatTrans.id_app] using congr_app hιπ n,
          Category.comp_id]
      uniq := by
        intro s m hm
        have hmi : m ≫ i = ha.lift { pt := s.pt, π := s.π ≫ ι } := by
          apply ha.uniq { pt := s.pt, π := s.π ≫ ι } (m ≫ i)
          intro n
          change (m ≫ i) ≫ F.map ((finitePerfectAdicCoefficientCone X d).π.app n) =
            s.π.app n ≫ ι.app n
          rw [Category.assoc, hi n, ← Category.assoc, hm n]
        rw [← hmi, Category.assoc, hip, Category.comp_id] }
  have hB (n : ℕ) : Epi (B.map (homOfLE n.le_succ).op) := by
    have (n : ℕᵒᵖ) : IsSplitEpi (π.app n) :=
      IsSplitEpi.mk' ⟨ι.app n, congr_app hιπ n⟩
    have := finitePerfectAdicCoefficientStep_epi X d n
    have : F.PreservesEpimorphisms := by dsimp [F]; infer_instance
    have : Epi ((finitePerfectAdicCoefficientDiagram X d ⋙ F).map
        (homOfLE n.le_succ).op) := by
      simpa only [Functor.comp_map, finitePerfectAdicCoefficientDiagram,
        Functor.ofOpSequence_map_homOfLE_succ] using
        (inferInstance : Epi (F.map (completedAdicFiniteModuleStep X d n)))
    exact epi_of_epi_fac (π.naturality (homOfLE n.le_succ).op).symm
  refine ⟨⟨hc⟩, hB, ?_⟩
  let S := HomologicalComplex.single (CompletedAdicModules X d) (.up ℤ) 0
  apply finitePerfectAdicComplex_roos X d (B ⋙ S) _ (S.mapCone c)
    (isLimitOfPreserves S hc)
  intro n j
  have := hB n
  change Epi ((HomologicalComplex.eval (CompletedAdicModules X d) (.up ℤ) j).map
    (S.map (B.map (homOfLE n.le_succ).op)))
  infer_instance

/-- A compatible finite-free retract of one degree of a coefficient tower and its cone.
The two cone equations retain the actual coefficient projections.
Source: Stacks Tag 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-coefficient-limit). -/
structure FinitePerfectAdicCoefficientRetract (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (B : ℕᵒᵖ ⥤ CompletedAdicModules X d) (c : Cone B) where
  rank : ℕ
  inclusion : B ⟶ finitePerfectAdicCoefficientDiagram X d ⋙
    Functor.const (Discrete (Fin rank)) ⋙ lim
  projection : finitePerfectAdicCoefficientDiagram X d ⋙
    Functor.const (Discrete (Fin rank)) ⋙ lim ⟶ B
  splitting : inclusion ≫ projection = 𝟙 B
  coneInclusion : c.pt ⟶ (lim (J := Discrete (Fin rank))).obj
    ((Functor.const (Discrete (Fin rank))).obj (SheafOfModules.unit (completedAdicRing X d)))
  coneProjection : (lim (J := Discrete (Fin rank))).obj
    ((Functor.const (Discrete (Fin rank))).obj (SheafOfModules.unit (completedAdicRing X d)))
      ⟶ c.pt
  coneSplitting : coneInclusion ≫ coneProjection = 𝟙 c.pt
  inclusion_naturality : ∀ n : ℕᵒᵖ, coneInclusion ≫
    (Functor.const (Discrete (Fin rank)) ⋙ lim).map
      ((finitePerfectAdicCoefficientCone X d).π.app n) = c.π.app n ≫ inclusion.app n
  projection_naturality : ∀ n : ℕᵒᵖ, coneProjection ≫ c.π.app n =
    (Functor.const (Discrete (Fin rank)) ⋙ lim).map
      ((finitePerfectAdicCoefficientCone X d).π.app n) ≫ projection.app n

/-- A coefficient complex tower with compatible finite-free retracts in every degree
has its specified completed cone as its Roos derived limit.

Source: Stacks Project, Tag 09C6, the finite-projective complex inverse-limit calculation.
(blueprint: lem-weil-pbc-finite-perfect-adic-coefficient-limit).

Proof: in each degree the compatible retract theorem proves that the given cone is
limiting and the consecutive maps are epimorphic. Evaluation jointly reflects limits
of complexes, so the original complex cone is limiting. Apply the epimorphic-complex
Roos theorem. Ranks may vary with the degree, and zero ranks are allowed. The theorem
requires the actual compatible retracts, rather than merely unrelated levelwise
finite-projectivity assertions. No boundedness is necessary for this Roos assertion. -/
theorem finitePerfectAdicProjectiveComplex_roos (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A)
    (T : ℕᵒᵖ ⥤ CochainComplex (CompletedAdicModules X d) ℤ) (c : Cone T)
    (h : ∀ j : ℤ, Nonempty (FinitePerfectAdicCoefficientRetract X d
      (T ⋙ HomologicalComplex.eval (CompletedAdicModules X d) (.up ℤ) j)
      ((HomologicalComplex.eval (CompletedAdicModules X d) (.up ℤ) j).mapCone c))) :
    HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (T.obj (op n))) ∧
    ∀ [HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj (T.obj (op n)))],
      IsDerivedLimit (K := fun n : ℕ ↦ DerivedCategory.Q.obj (T.obj (op n)))
        (fun n : ℕ ↦ DerivedCategory.Q.map (T.map (homOfLE n.le_succ).op))
        (DerivedCategory.Q.obj c.pt) := by
  classical
  let R (j : ℤ) := (h j).some
  have hj (j : ℤ) := finitePerfectAdicRetract_roos X d (R j).rank _
    (R j).inclusion (R j).projection (R j).splitting _
    (R j).coneInclusion (R j).coneProjection (R j).coneSplitting
    (R j).inclusion_naturality (R j).projection_naturality
  let hc : IsLimit c := HomologicalComplex.isLimitOfEval T c (fun j ↦ (hj j).1.some)
  apply finitePerfectAdicComplex_roos X d T _ c hc
  intro n j
  exact (hj j).2.1 n

end AlgebraicGeometry.Scheme
