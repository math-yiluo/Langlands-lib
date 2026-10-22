import Langlands.Cohomology.DivisibleSystem.Cokernel
import Langlands.Cohomology.CokernelComplex
import Langlands.Cohomology.SmoothGodement.Statement

/-!
# Coaugmented exact functors and `ℓ`-divisible systems

Harris 1999, §2, p.304: for an exact functor `F` with a monic coaugmentation
`η : 𝟭 ⟶ F`, the canonical embeddings `b_m : T m ⟶ F (T m)` form a morphism of
`ℓ`-divisible systems `T ⟶ F(T)`, its cokernel is again an `ℓ`-divisible system, and
iterating gives `ℓ`-divisible systems `R q` and `F^q = F(R q)` with the maps of the
cokernel construction between them. At every level `m` these are the residual and term
objects of `CokernelComplex` at `T m`, and the maps form a resolution of `T m`.
The specialization to the smooth Godement functor takes the exactness of its degree-zero
functor as a hypothesis.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace DivisibleSystem

section Coaugmented

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}
variable (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (η : 𝟭 C ⟶ F)

/-- The morphism `b : T ⟶ F(T)` of `ℓ`-divisible systems with components
`b_m = η (T m)`. -/
def coaugmentation (T : DivisibleSystem C ℓ) : T ⟶ T.map F where
  tower :=
    { app := fun m => η.app (T.tower.obj m)
      naturality := fun _ _ f => η.naturality (T.tower.map f) }
  comm h := η.naturality (T.inclusion h)

lemma coaugmentation_tower_app (T : DivisibleSystem C ℓ) (m : ℕᵒᵖ) :
    (T.coaugmentation F η).tower.app m = η.app (T.tower.obj m) :=
  rfl

variable [∀ X : C, Mono (η.app X)]

instance mono_coaugmentation_tower_app (T : DivisibleSystem C ℓ) (m : ℕᵒᵖ) :
    Mono ((T.coaugmentation F η).tower.app m) :=
  show Mono (η.app _) from inferInstance

variable (T : DivisibleSystem C ℓ)

/-- The residual systems: `R 0 = T` and `R (q + 1) = coker (R q ⟶ F(R q))`. -/
def residualSystem : ℕ → DivisibleSystem C ℓ
  | 0 => T
  | q + 1 => cokernelSystem ((residualSystem q).coaugmentation F η)

@[simp]
lemma residualSystem_zero : T.residualSystem F η 0 = T :=
  rfl

lemma residualSystem_succ (q : ℕ) :
    T.residualSystem F η (q + 1) = cokernelSystem ((T.residualSystem F η q).coaugmentation F η) :=
  rfl

/-- The term systems `F^q = F(R q)`. -/
abbrev termSystem (q : ℕ) : DivisibleSystem C ℓ :=
  (T.residualSystem F η q).map F

/-- The coaugmentation `R q ⟶ F^q`. -/
def residualInclusion (q : ℕ) : T.residualSystem F η q ⟶ T.termSystem F η q :=
  (T.residualSystem F η q).coaugmentation F η

/-- The projection `F^q ⟶ R (q + 1)` onto the cokernel system. -/
def residualQuotient (q : ℕ) : T.termSystem F η q ⟶ T.residualSystem F η (q + 1) :=
  toCokernelSystem ((T.residualSystem F η q).coaugmentation F η)

/-- The differential `F^q ⟶ F^(q + 1)`: the projection followed by the coaugmentation. -/
def termDifferential (q : ℕ) : T.termSystem F η q ⟶ T.termSystem F η (q + 1) :=
  T.residualQuotient F η q ≫ T.residualInclusion F η (q + 1)

lemma residualInclusion_tower_app (q : ℕ) (m : ℕᵒᵖ) :
    (T.residualInclusion F η q).tower.app m = η.app ((T.residualSystem F η q).tower.obj m) :=
  rfl

lemma termDifferential_tower_app (q : ℕ) (m : ℕᵒᵖ) :
    (T.termDifferential F η q).tower.app m =
      (T.residualQuotient F η q).tower.app m ≫ (T.residualInclusion F η (q + 1)).tower.app m :=
  rfl

instance mono_residualInclusion_tower_app (q : ℕ) (m : ℕᵒᵖ) :
    Mono ((T.residualInclusion F η q).tower.app m) :=
  show Mono (η.app _) from inferInstance

instance epi_residualQuotient_tower_app (q : ℕ) (m : ℕᵒᵖ) :
    Epi ((T.residualQuotient F η q).tower.app m) :=
  show Epi ((toCokernelSystem ((T.residualSystem F η q).coaugmentation F η)).tower.app m)
    from inferInstance

@[reassoc (attr := simp)]
lemma residualInclusion_residualQuotient_tower_app (q : ℕ) (m : ℕᵒᵖ) :
    (T.residualInclusion F η q).tower.app m ≫ (T.residualQuotient F η q).tower.app m = 0 :=
  comp_toCokernelSystem_tower_app _ m

/-- Each level `0 ⟶ R q ⟶ F^q ⟶ R (q + 1) ⟶ 0` is short exact. -/
lemma residual_shortExact (q m : ℕ) :
    (ShortComplex.mk ((T.residualInclusion F η q).tower.app (op m))
      ((T.residualQuotient F η q).tower.app (op m))
      (T.residualInclusion_residualQuotient_tower_app F η q _)).ShortExact :=
  shortExact_app _ m

@[reassoc (attr := simp)]
lemma residualInclusion_termDifferential_tower_app (q : ℕ) (m : ℕᵒᵖ) :
    (T.residualInclusion F η q).tower.app m ≫ (T.termDifferential F η q).tower.app m = 0 := by
  rw [termDifferential_tower_app, residualInclusion_residualQuotient_tower_app_assoc, zero_comp]

@[reassoc (attr := simp)]
lemma termDifferential_comp_termDifferential_tower_app (q : ℕ) (m : ℕᵒᵖ) :
    (T.termDifferential F η q).tower.app m ≫ (T.termDifferential F η (q + 1)).tower.app m =
      0 := by
  rw [termDifferential_tower_app, Category.assoc,
    residualInclusion_termDifferential_tower_app, comp_zero]

/-- Exactness of `R q ⟶ F^q ⟶ F^(q + 1)` at every level. For `q = 0` this is exactness of
the augmented resolution `0 ⟶ T m ⟶ F^0 ⟶ F^1` at `F^0`. -/
lemma residualInclusion_termDifferential_exact (q m : ℕ) :
    (ShortComplex.mk ((T.residualInclusion F η q).tower.app (op m))
      ((T.termDifferential F η q).tower.app (op m))
      (T.residualInclusion_termDifferential_tower_app F η q _)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x hx
  have h₁ : x ≫ (T.residualQuotient F η q).tower.app (op m) = 0 := by
    rw [← cancel_mono ((T.residualInclusion F η (q + 1)).tower.app (op m)), zero_comp,
      Category.assoc]
    exact hx
  exact (T.residual_shortExact F η q m).exact.exact_up_to_refinements x h₁

/-- Exactness of `F^q ⟶ F^(q + 1) ⟶ F^(q + 2)` at every level. -/
lemma termDifferential_exact (q m : ℕ) :
    (ShortComplex.mk ((T.termDifferential F η q).tower.app (op m))
      ((T.termDifferential F η (q + 1)).tower.app (op m))
      (T.termDifferential_comp_termDifferential_tower_app F η q _)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x hx
  obtain ⟨A₁, π₁, _, y, hy⟩ :=
    (T.residualInclusion_termDifferential_exact F η (q + 1) m).exact_up_to_refinements x hx
  obtain ⟨A₂, π₂, _, z, hz⟩ :=
    surjective_up_to_refinements_of_epi ((T.residualQuotient F η q).tower.app (op m)) y
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, z, ?_⟩
  change (π₂ ≫ π₁) ≫ x = z ≫ (T.termDifferential F η q).tower.app (op m)
  change π₁ ≫ x = y ≫ (T.residualInclusion F η (q + 1)).tower.app (op m) at hy
  rw [Category.assoc, hy, reassoc_of% hz]
  rfl

/-- The levels of `R q` are the residual objects of the cokernel construction at `T m`. -/
def residualSystemObjIso : (q : ℕ) → (m : ℕᵒᵖ) →
    ((T.residualSystem F η q).tower.obj m ≅ (CokernelComplex.residual F η q).obj (T.tower.obj m))
  | 0, _ => Iso.refl _
  | q + 1, m =>
    (cokernel.mapIso (η.app ((T.residualSystem F η q).tower.obj m))
      (η.app ((CokernelComplex.residual F η q).obj (T.tower.obj m)))
      (residualSystemObjIso q m) (F.mapIso (residualSystemObjIso q m))
      (η.naturality _).symm :) ≪≫
    (PreservesCokernel.iso ((evaluation C C).obj (T.tower.obj m))
      (Functor.whiskerLeft (CokernelComplex.residual F η q) η)).symm

/-- The levels of `F^q` are the terms of the cokernel construction at `T m`. -/
def termSystemObjIso (q : ℕ) (m : ℕᵒᵖ) :
    (T.termSystem F η q).tower.obj m ≅ (CokernelComplex.term F η q).obj (T.tower.obj m) :=
  F.mapIso (T.residualSystemObjIso F η q m)

lemma residualInclusion_comp_termSystemObjIso_hom (q : ℕ) (m : ℕᵒᵖ) :
    (T.residualInclusion F η q).tower.app m ≫ (T.termSystemObjIso F η q m).hom =
      (T.residualSystemObjIso F η q m).hom ≫
        (CokernelComplex.inclusion F η q).app (T.tower.obj m) :=
  (η.naturality _).symm

lemma residualQuotient_comp_residualSystemObjIso_hom (q : ℕ) (m : ℕᵒᵖ) :
    (T.residualQuotient F η q).tower.app m ≫ (T.residualSystemObjIso F η (q + 1) m).hom =
      (T.termSystemObjIso F η q m).hom ≫
        (CokernelComplex.quotient F η q).app (T.tower.obj m) := by
  change cokernel.π (η.app ((T.residualSystem F η q).tower.obj m)) ≫
      (cokernel.mapIso (η.app ((T.residualSystem F η q).tower.obj m))
        (η.app ((CokernelComplex.residual F η q).obj (T.tower.obj m)))
        (T.residualSystemObjIso F η q m) (F.mapIso (T.residualSystemObjIso F η q m))
        (η.naturality _).symm).hom ≫
      (PreservesCokernel.iso ((evaluation C C).obj (T.tower.obj m))
        (Functor.whiskerLeft (CokernelComplex.residual F η q) η)).inv =
    F.map (T.residualSystemObjIso F η q m).hom ≫
      (cokernel.π (Functor.whiskerLeft (CokernelComplex.residual F η q) η)).app
        (T.tower.obj m)
  rw [cokernel.mapIso_hom, cokernel.π_desc_assoc, Category.assoc, PreservesCokernel.iso_inv]
  exact congrArg (F.map (T.residualSystemObjIso F η q m).hom ≫ ·)
    (π_comp_cokernelComparison (Functor.whiskerLeft (CokernelComplex.residual F η q) η)
      ((evaluation C C).obj (T.tower.obj m)))

/-- Under the level isomorphisms, the differentials of the term systems are the
differentials of the cokernel construction at `T m`. -/
lemma termDifferential_comp_termSystemObjIso_hom (q : ℕ) (m : ℕᵒᵖ) :
    (T.termDifferential F η q).tower.app m ≫ (T.termSystemObjIso F η (q + 1) m).hom =
      (T.termSystemObjIso F η q m).hom ≫
        (CokernelComplex.differential F η q).app (T.tower.obj m) := by
  rw [termDifferential_tower_app, Category.assoc, residualInclusion_comp_termSystemObjIso_hom,
    reassoc_of% T.residualQuotient_comp_residualSystemObjIso_hom F η q m]
  rfl

end Coaugmented

section Smooth

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)

/-- The residual systems `R q` of an `ℓ`-divisible system of smooth sheaves for the smooth
Godement functor, given that its degree-zero functor is exact. -/
def smoothGodementResidualSystem (q : ℕ) : SmoothSheafDivisibleSystem R G X ℓ :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  residualSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) T q

/-- The term systems `F^q` of Harris's Lemma 2.2 for the smooth Godement functor, given
that its degree-zero functor is exact. -/
def smoothGodementTermSystem (q : ℕ) : SmoothSheafDivisibleSystem R G X ℓ :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  termSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) T q

/-- Harris's morphism `b : T ⟶ F^0` for the smooth Godement functor. -/
def smoothGodementCoaugmentation : T ⟶ smoothGodementTermSystem h T 0 :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  residualInclusion (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) T 0

/-- The differential `F^q ⟶ F^(q + 1)` for the smooth Godement functor. -/
def smoothGodementTermDifferential (q : ℕ) :
    smoothGodementTermSystem h T q ⟶ smoothGodementTermSystem h T (q + 1) :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  termDifferential (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) T q

/-- The levels of the smooth Godement term systems are the terms of the smooth Godement
complexes of the levels of `T`. -/
def smoothGodementTermSystemObjIso (q m : ℕ) :
    (smoothGodementTermSystem h T q).obj m ≅ (smoothComplex R G X (T.obj m)).X q :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  termSystemObjIso (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) T q (op m)

/-- Under the level isomorphisms, the differentials of the smooth Godement term systems are
the differentials of the smooth Godement complexes of the levels of `T`. -/
lemma smoothGodementTermDifferential_comp_termSystemObjIso_hom (q m : ℕ) :
    (smoothGodementTermDifferential h T q).tower.app (op m) ≫
        (smoothGodementTermSystemObjIso h T (q + 1) m).hom =
      (smoothGodementTermSystemObjIso h T q m).hom ≫
        (smoothComplex R G X (T.obj m)).d q (q + 1) := by
  have := h.1
  have := h.2.1
  have := h.2.2
  exact (termDifferential_comp_termSystemObjIso_hom (smoothZeroFunctor R G X)
    (smoothCoaugmentation R G X) T q (op m)).trans
    (congrArg ((smoothGodementTermSystemObjIso h T q m).hom ≫ ·)
      (CokernelComplex.complex_d (smoothZeroFunctor R G X) (smoothCoaugmentation R G X)
        (T.obj m) q).symm)

end Smooth

end DivisibleSystem

end Langlands.Cohomology
