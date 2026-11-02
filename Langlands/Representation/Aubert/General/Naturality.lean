import Langlands.Representation.Aubert.General.Terminal

/-! Naturality of the actual normalized complex and its retained terminal quotient. -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.Complex

open CategoryTheory

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
variable (h : ∀ s, IsSemidirectDecomposition (P s) (M s) (U s))
variable (hclosed : ∀ s, IsClosed (U s : Set G))
variable (hδ : ∀ s, IsUnimodularModulus (U s) (hclosed s))
variable (hP : Antitone P) (hU : Monotone U)
variable {A B C : SmoothRep.{0, uG, max uG uV} ℂ G}

/-- The actual normalized functor applied to an ambient morphism. -/
def termMap (φ : A ⟶ B) (s : Finset ι) :
    (termRepresentation P M U h hclosed A s).IntertwiningMap
      (termRepresentation P M U h hclosed B s) :=
  SmoothRep.hom ((inductionJacquetFunctor.{uG, uV} (h s) (hclosed s)).map φ)

omit [LinearOrder ι] [Fintype ι] in
/-- Normalization intertwines actual functor maps with pointwise coinvariant maps. -/
theorem termEquiv_map (φ : A ⟶ B) (s : Finset ι) (f : Term P M U h hclosed A s) :
    termEquiv P M U h hclosed hδ B s (termMap P M U h hclosed φ s f) =
      SubgroupTransition.termMap (P s) (U s) (h s).le_normalizer (SmoothRep.hom φ)
        (termEquiv P M U h hclosed hδ A s f) :=
  LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap
    (inductionJacquetTermIso_natural (h s) (hclosed s) (hδ s) φ)) f

omit [Fintype ι] in
/-- The actual normalized functor maps commute with every canonical transition. -/
theorem termMap_natural (φ : A ⟶ B) {s t : Finset ι} (hst : s ⊆ t) :
    (termMap P M U h hclosed φ t).toLinearMap ∘ₗ
        (transition P M U h hclosed hδ hP hU A hst).toLinearMap =
      (transition P M U h hclosed hδ hP hU B hst).toLinearMap ∘ₗ
        (termMap P M U h hclosed φ s).toLinearMap := by
  apply LinearMap.ext
  intro f
  apply (termEquiv P M U h hclosed hδ B t).injective
  change termEquiv P M U h hclosed hδ B t
      (termMap P M U h hclosed φ t (transition P M U h hclosed hδ hP hU A hst f)) =
    termEquiv P M U h hclosed hδ B t
      (transition P M U h hclosed hδ hP hU B hst (termMap P M U h hclosed φ s f))
  rw [termEquiv_map, termEquiv_transition, termEquiv_transition, termEquiv_map]
  exact LinearMap.congr_fun
    (SubgroupComplex.objectMap_natural P U (fun s => (h s).le_normalizer)
      hP hU (SmoothRep.hom φ) hst) _

omit [LinearOrder ι] [Fintype ι] in
theorem termMap_id (s : Finset ι) :
    termMap P M U h hclosed (𝟙 A) s =
      Representation.IntertwiningMap.id (termRepresentation P M U h hclosed A s) := by
  change SmoothRep.hom ((inductionJacquetFunctor.{uG, uV} (h s) (hclosed s)).map (𝟙 A)) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

omit [LinearOrder ι] [Fintype ι] in
theorem termMap_comp (φ : A ⟶ B) (ψ : B ⟶ C) (s : Finset ι) :
    termMap P M U h hclosed (φ ≫ ψ) s =
      (termMap P M U h hclosed ψ s).comp (termMap P M U h hclosed φ s) := by
  change SmoothRep.hom ((inductionJacquetFunctor.{uG, uV} (h s) (hclosed s)).map (φ ≫ ψ)) = _
  rw [CategoryTheory.Functor.map_comp]
  rfl

/-- The actual equivariant map in a homogeneous degree. -/
def degreeMap (φ : A ⟶ B) (k : ℕ) :
    (degreeRepresentation P M U h hclosed A k).IntertwiningMap
      (degreeRepresentation P M U h hclosed B k) where
  toLinearMap := CutComplex.Diagram.mapDegree
    (diagram P M U h hclosed hδ hP hU A) (diagram P M U h hclosed hδ hP hU B)
    (fun s => (termMap P M U h hclosed φ s).toLinearMap) k
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext s
    exact LinearMap.congr_fun ((termMap P M U h hclosed φ s.1).isIntertwining' g) (x s)

/-- Naturality holds for the unchanged exterior signs in the differential. -/
theorem degreeMap_differential (φ : A ⟶ B) (k : ℕ) :
    (degreeMap P M U h hclosed hδ hP hU φ (k + 1)).comp
        (differential P M U h hclosed hδ hP hU A k) =
      (differential P M U h hclosed hδ hP hU B k).comp
        (degreeMap P M U h hclosed hδ hP hU φ k) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  exact CutComplex.Diagram.mapDegree_differential
    (diagram P M U h hclosed hδ hP hU A) (diagram P M U h hclosed hδ hP hU B)
    (fun s => (termMap P M U h hclosed φ s).toLinearMap)
    (termMap_natural P M U h hclosed hδ hP hU φ) k

omit [Fintype ι] in
theorem degreeMap_id (k : ℕ) :
    degreeMap P M U h hclosed hδ hP hU (𝟙 A) k =
      Representation.IntertwiningMap.id (degreeRepresentation P M U h hclosed A k) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  funext s
  exact LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap
    (termMap_id P M U h hclosed (A := A) s.1)) (x s)

omit [Fintype ι] in
theorem degreeMap_comp (φ : A ⟶ B) (ψ : B ⟶ C) (k : ℕ) :
    degreeMap P M U h hclosed hδ hP hU (φ ≫ ψ) k =
      (degreeMap P M U h hclosed hδ hP hU ψ k).comp
        (degreeMap P M U h hclosed hδ hP hU φ k) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  funext s
  exact LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap
    (termMap_comp P M U h hclosed φ ψ s.1)) (x s)

/-- The homogeneous objects form a functor on the full smooth category. -/
def degreeFunctor (k : ℕ) :
    SmoothRep.{0, uG, max uG uV} ℂ G ⥤ SmoothRep.{0, uG, max uI uG uV} ℂ G where
  obj A := degreeObject P M U h hclosed A k
  map φ := SmoothRep.ofHom (degreeMap P M U h hclosed hδ hP hU φ k)
  map_id A := by
    apply (SmoothRep.toRep).map_injective
    apply Rep.hom_ext
    exact degreeMap_id P M U h hclosed hδ hP hU k
  map_comp φ ψ := by
    apply (SmoothRep.toRep).map_injective
    apply Rep.hom_ext
    exact degreeMap_comp P M U h hclosed hδ hP hU φ ψ k

/-- A chain map carries incoming boundaries into incoming boundaries. -/
theorem boundary_map_le (φ : A ⟶ B) (k : ℕ) :
    boundary P M U h hclosed hδ hP hU A k ≤
      (boundary P M U h hclosed hδ hP hU B k).comap
        (degreeMap P M U h hclosed hδ hP hU φ k).toLinearMap := by
  cases k with
  | zero => exact bot_le
  | succ k =>
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨degreeMap P M U h hclosed hδ hP hU φ k y,
      (LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap
        (degreeMap_differential P M U h hclosed hδ hP hU φ k)) y).symm⟩

/-- The map induced on the actual retained terminal quotient. -/
def terminalMap (φ : A ⟶ B) (k : ℕ) :
    (terminalRepresentation P M U h hclosed hδ hP hU A k).IntertwiningMap
      (terminalRepresentation P M U h hclosed hδ hP hU B k) where
  toLinearMap := Submodule.mapQ
    (boundary P M U h hclosed hδ hP hU A k) (boundary P M U h hclosed hδ hP hU B k)
    (degreeMap P M U h hclosed hδ hP hU φ k).toLinearMap
    (boundary_map_le P M U h hclosed hδ hP hU φ k)
  isIntertwining' g := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext
    intro x
    change (boundary P M U h hclosed hδ hP hU B k).mkQ
        (degreeMap P M U h hclosed hδ hP hU φ k
          (degreeRepresentation P M U h hclosed A k g x)) =
      (boundary P M U h hclosed hδ hP hU B k).mkQ
        (degreeRepresentation P M U h hclosed B k g
          (degreeMap P M U h hclosed hδ hP hU φ k x))
    exact congrArg (boundary P M U h hclosed hδ hP hU B k).mkQ
      (LinearMap.congr_fun ((degreeMap P M U h hclosed hδ hP hU φ k).isIntertwining' g) x)

/-- Naturality of the quotient projection, without a terminal vanishing premise. -/
theorem terminalMap_comp_projection (φ : A ⟶ B) (k : ℕ) :
    (terminalMap P M U h hclosed hδ hP hU φ k).comp
        (terminalProjection P M U h hclosed hδ hP hU A k) =
      (terminalProjection P M U h hclosed hδ hP hU B k).comp
        (degreeMap P M U h hclosed hδ hP hU φ k) := by
  apply Representation.IntertwiningMap.ext
  rfl

/-- The quotient map respects the identity ambient morphism. -/
theorem terminalMap_id (k : ℕ) :
    terminalMap P M U h hclosed hδ hP hU (𝟙 A) k =
      Representation.IntertwiningMap.id
        (terminalRepresentation P M U h hclosed hδ hP hU A k) := by
  apply Representation.IntertwiningMap.ext
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro x
  change (boundary P M U h hclosed hδ hP hU A k).mkQ
    (degreeMap P M U h hclosed hδ hP hU (𝟙 A) k x) = _
  rw [degreeMap_id]
  rfl

/-- The quotient map respects composition of actual ambient morphisms. -/
theorem terminalMap_comp (φ : A ⟶ B) (ψ : B ⟶ C) (k : ℕ) :
    terminalMap P M U h hclosed hδ hP hU (φ ≫ ψ) k =
      (terminalMap P M U h hclosed hδ hP hU ψ k).comp
        (terminalMap P M U h hclosed hδ hP hU φ k) := by
  apply Representation.IntertwiningMap.ext
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro x
  change (boundary P M U h hclosed hδ hP hU C k).mkQ
    (degreeMap P M U h hclosed hδ hP hU (φ ≫ ψ) k x) = _
  rw [degreeMap_comp]
  rfl

/-- The actual terminal cokernel construction is functorial on all smooth objects. -/
def terminalFunctor (k : ℕ) :
    SmoothRep.{0, uG, max uG uV} ℂ G ⥤ SmoothRep.{0, uG, max uI uG uV} ℂ G where
  obj A := terminalObject P M U h hclosed hδ hP hU A k
  map φ := SmoothRep.ofHom (terminalMap P M U h hclosed hδ hP hU φ k)
  map_id A := by
    apply (SmoothRep.toRep).map_injective
    apply Rep.hom_ext
    exact terminalMap_id P M U h hclosed hδ hP hU k
  map_comp φ ψ := by
    apply (SmoothRep.toRep).map_injective
    apply Rep.hom_ext
    exact terminalMap_comp P M U h hclosed hδ hP hU φ ψ k

/-- The retained terminal cokernel functor at support rank `|I|`. -/
abbrev sharpFunctor (I : Finset ι) :=
  terminalFunctor P M U h hclosed hδ hP hU (terminalDegree I)

/-- The actual signed differentials are natural transformations. -/
def differentialNat (k : ℕ) :
    degreeFunctor P M U h hclosed hδ hP hU k ⟶
      degreeFunctor P M U h hclosed hδ hP hU (k + 1) where
  app A := degreeMorphism P M U h hclosed hδ hP hU A k
  naturality _ _ φ := by
    apply (SmoothRep.toRep).map_injective
    apply Rep.hom_ext
    exact (degreeMap_differential P M U h hclosed hδ hP hU φ k).symm

/-- The canonical quotient projections form a natural transformation. -/
def terminalProjectionNat (k : ℕ) :
    degreeFunctor P M U h hclosed hδ hP hU k ⟶
      terminalFunctor P M U h hclosed hδ hP hU k where
  app A := SmoothRep.ofHom (terminalProjection P M U h hclosed hδ hP hU A k)
  naturality _ _ φ := by
    apply (SmoothRep.toRep).map_injective
    apply Rep.hom_ext
    exact (terminalMap_comp_projection P M U h hclosed hδ hP hU φ k).symm

end Langlands.Aubert.General.Complex
