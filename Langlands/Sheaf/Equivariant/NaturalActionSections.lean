import Langlands.Sheaf.Equivariant.LocalActionCohomology

/-!
# Sections and invariant sections along a natural action

Let `Φ : E ⥤ T` be a functor, and let a monoid `K` act on every object `Φ V` by
endomorphisms, compatibly with the images of the morphisms of `E`. Then the sections
over the objects `Φ V` of a module presheaf on `T` form a presheaf on `E` of
representations of `K`. Their `K`-invariants form a presheaf of modules on `E`. Both
constructions are functorial in the module presheaf, and left exact. For a `G`-space
`X`, the presheaf of invariants is the presheaf `V(G) ↦ F(V)^G` in the proof of
Berkovich's Theorem 1.4.2. That case is `AnalyticInvariantPresheaf`.

For a topological group `G` and a local action system on `T`, if the restriction of
the action on `Φ V` to the open subgroup `G` is admissible, then the sections over `Φ V`
of a discrete presheaf form a smooth representation of `G`.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits Opposite

universe v u vE uE vE' uE' uK uG uR w

variable {T : Type u} [Category.{v} T] {E : Type uE} [Category.{vE} E]

/-- A natural action of a monoid `K` along a functor `Φ : E ⥤ T`: an action of `K` on each
object `Φ V` by endomorphisms, such that the images under `Φ` of the morphisms of `E`
commute with the actions. -/
structure NaturalAction (K : Type uK) [Monoid K] (Φ : E ⥤ T) where
  /-- The action of `K` on `Φ V`. -/
  act : ∀ V : E, K →* (End (Φ.obj V))ᵐᵒᵖ
  /-- The images of the morphisms of `E` commute with the actions. -/
  comm : ∀ {V W : E} (f : V ⟶ W) (k : K),
    (act V k).unop ≫ Φ.map f = Φ.map f ≫ (act W k).unop

namespace NaturalAction

variable {K : Type uK} [Monoid K] {Φ : E ⥤ T} (a : NaturalAction K Φ)

section Precomp

variable {E' : Type uE'} [Category.{vE'} E']

/-- Precomposition of a natural action along `Φ` with a functor `Ψ : E' ⥤ E`. -/
def precomp (Ψ : E' ⥤ E) : NaturalAction K (Ψ ⋙ Φ) where
  act V := a.act (Ψ.obj V)
  comm f k := a.comm (Ψ.map f) k

@[simp]
theorem precomp_act (Ψ : E' ⥤ E) (V : E') : (a.precomp Ψ).act V = a.act (Ψ.obj V) :=
  rfl

end Precomp

variable (R : Type uR) [CommRing R]

/-- Restriction along `Φ f` intertwines the actions on sections. -/
def sectionsIntertwiningMap (F : Tᵒᵖ ⥤ ModuleCat.{w} R) {V W : E} (f : V ⟶ W) :
    (actionRepresentation F (a.act W)).IntertwiningMap (actionRepresentation F (a.act V)) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap (actionRepresentation F (a.act W))
    (actionRepresentation F (a.act V)) (F.map (Φ.map f).op).hom fun k s => by
      rw [actionRepresentation_apply, actionRepresentation_apply]
      change (F.map (a.act W k).unop.op ≫ F.map (Φ.map f).op).hom s =
        (F.map (Φ.map f).op ≫ F.map (a.act V k).unop.op).hom s
      rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, a.comm]

@[simp]
theorem sectionsIntertwiningMap_apply (F : Tᵒᵖ ⥤ ModuleCat.{w} R) {V W : E} (f : V ⟶ W)
    (s : F.obj (op (Φ.obj W))) :
    a.sectionsIntertwiningMap R F f s = (F.map (Φ.map f).op).hom s :=
  rfl

/-- The sections over the objects `Φ V` of a module presheaf, as a presheaf on `E` of
representations of `K`. -/
def sectionsRepPresheaf (F : Tᵒᵖ ⥤ ModuleCat.{w} R) : Eᵒᵖ ⥤ Rep.{w} R K where
  obj V := (sectionsRep R (a.act V.unop)).obj F
  map f := Rep.ofHom (a.sectionsIntertwiningMap R F f.unop)
  map_id V := by
    ext s
    change (F.map (Φ.map (𝟙 V.unop)).op).hom s = s
    rw [Φ.map_id, op_id, F.map_id]
    rfl
  map_comp f g := by
    ext s
    change (F.map (Φ.map (g.unop ≫ f.unop)).op).hom s =
      (F.map (Φ.map g.unop).op).hom ((F.map (Φ.map f.unop).op).hom s)
    rw [Φ.map_comp, op_comp, F.map_comp]
    rfl

@[simp]
theorem sectionsRepPresheaf_obj_ρ (F : Tᵒᵖ ⥤ ModuleCat.{w} R) (V : E) :
    ((a.sectionsRepPresheaf R F).obj (op V)).ρ = actionRepresentation F (a.act V) :=
  rfl

@[simp]
theorem sectionsRepPresheaf_map_hom_apply (F : Tᵒᵖ ⥤ ModuleCat.{w} R) {V W : E} (f : V ⟶ W)
    (s : F.obj (op (Φ.obj W))) :
    ((a.sectionsRepPresheaf R F).map f.op).hom s = (F.map (Φ.map f).op).hom s :=
  rfl

/-- The presheaf of section representations, functorially in the module presheaf. -/
def sectionsRepFunctor : (Tᵒᵖ ⥤ ModuleCat.{w} R) ⥤ (Eᵒᵖ ⥤ Rep.{w} R K) where
  obj F := a.sectionsRepPresheaf R F
  map {F F'} φ :=
    { app := fun V => (sectionsRep R (a.act V.unop)).map φ
      naturality := fun V W f => by
        ext s
        change (φ.app _).hom ((F.map (Φ.map f.unop).op).hom s) =
          (F'.map (Φ.map f.unop).op).hom ((φ.app _).hom s)
        exact NatTrans.naturality_apply φ (Φ.map f.unop).op s }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
theorem sectionsRepFunctor_obj (F : Tᵒᵖ ⥤ ModuleCat.{w} R) :
    (a.sectionsRepFunctor R).obj F = a.sectionsRepPresheaf R F :=
  rfl

/-- Evaluating the presheaf of section representations at `V` is the representation on the
sections over `Φ V`. -/
theorem sectionsRepFunctor_comp_evaluation (V : E) :
    a.sectionsRepFunctor R ⋙ (evaluation Eᵒᵖ (Rep.{w} R K)).obj (op V) =
      sectionsRep R (a.act V) :=
  rfl

/-- Sections over an object with an action, as a representation, are left exact on module
presheaves. -/
instance sectionsRep_preservesFiniteLimits {U : T} (b : K →* (End U)ᵐᵒᵖ) :
    PreservesFiniteLimits
      (sectionsRep R b : (Tᵒᵖ ⥤ ModuleCat.{w} R) ⥤ Rep.{w} R K) := by
  have : PreservesFiniteLimits
      (sectionsRep R b ⋙ forget₂ (Rep.{w} R K) (ModuleCat.{w} R)) :=
    preservesFiniteLimits_of_natIso (sectionsRepForgetIso b).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} R K) (ModuleCat.{w} R))

/-- The presheaf of section representations is left exact in the module presheaf. -/
instance sectionsRepFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (a.sectionsRepFunctor R :
      (Tᵒᵖ ⥤ ModuleCat.{w} R) ⥤ (Eᵒᵖ ⥤ Rep.{w} R K)) :=
  preservesFiniteLimits_of_evaluation _ fun V =>
    inferInstanceAs (PreservesFiniteLimits (sectionsRep R (a.act V.unop)))

section Invariants

variable {K : Type uK} [Group K] {Φ : E ⥤ T} (a : NaturalAction K Φ)

/-- The presheaf `V ↦ F(Φ V)^K` of `K`-invariant sections. -/
def invariantPresheaf (F : Tᵒᵖ ⥤ ModuleCat.{w} R) : Eᵒᵖ ⥤ ModuleCat.{w} R :=
  a.sectionsRepPresheaf R F ⋙ Rep.invariantsFunctor R K

/-- A section over `Φ V` is invariant when it is fixed by the action of every element. -/
theorem mem_invariantPresheaf_obj_iff (F : Tᵒᵖ ⥤ ModuleCat.{w} R) (V : E)
    (s : F.obj (op (Φ.obj V))) :
    s ∈ (actionRepresentation F (a.act V)).invariants ↔
      ∀ k : K, (F.map (a.act V k).unop.op).hom s = s :=
  Iff.rfl

@[simp]
theorem invariantPresheaf_map_apply (F : Tᵒᵖ ⥤ ModuleCat.{w} R) {V W : E} (f : V ⟶ W)
    (s : (a.invariantPresheaf R F).obj (op W)) :
    (((a.invariantPresheaf R F).map f.op).hom s).1 = (F.map (Φ.map f).op).hom s.1 :=
  rfl

/-- The presheaf of invariant sections, functorially in the module presheaf. -/
def invariantFunctor : (Tᵒᵖ ⥤ ModuleCat.{w} R) ⥤ (Eᵒᵖ ⥤ ModuleCat.{w} R) :=
  a.sectionsRepFunctor R ⋙ (Functor.whiskeringRight Eᵒᵖ _ _).obj (Rep.invariantsFunctor R K)

@[simp]
theorem invariantFunctor_obj (F : Tᵒᵖ ⥤ ModuleCat.{w} R) :
    (a.invariantFunctor R).obj F = a.invariantPresheaf R F :=
  rfl

/-- Evaluating the presheaf of invariant sections at `V` is the invariants of the
representation on the sections over `Φ V`. -/
theorem invariantFunctor_comp_evaluation (V : E) :
    a.invariantFunctor R ⋙ (evaluation Eᵒᵖ (ModuleCat.{w} R)).obj (op V) =
      sectionsRep R (a.act V) ⋙ Rep.invariantsFunctor R K :=
  rfl

/-- The presheaf of invariant sections is left exact in the module presheaf. -/
instance invariantFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (a.invariantFunctor R :
      (Tᵒᵖ ⥤ ModuleCat.{w} R) ⥤ (Eᵒᵖ ⥤ ModuleCat.{w} R)) :=
  preservesFiniteLimits_of_evaluation _ fun V => by
    have := (Rep.invariantsAdjunction R K).rightAdjoint_preservesLimits
    exact inferInstanceAs
      (PreservesFiniteLimits (sectionsRep R (a.act V.unop) ⋙ Rep.invariantsFunctor R K))

/-- Precomposition with `Ψ` restricts the presheaf of invariant sections along `Ψ`. -/
theorem precomp_invariantPresheaf {E' : Type uE'} [Category.{vE'} E'] (Ψ : E' ⥤ E)
    (F : Tᵒᵖ ⥤ ModuleCat.{w} R) :
    (a.precomp Ψ).invariantPresheaf R F = Ψ.op ⋙ a.invariantPresheaf R F :=
  rfl

variable (J : GrothendieckTopology T)

/-- The presheaf of invariant sections of module sheaves. -/
def sheafInvariantFunctor : Sheaf J (ModuleCat.{w} R) ⥤ (Eᵒᵖ ⥤ ModuleCat.{w} R) :=
  sheafToPresheaf J (ModuleCat.{w} R) ⋙ a.invariantFunctor R

@[simp]
theorem sheafInvariantFunctor_obj (F : Sheaf J (ModuleCat.{w} R)) :
    (a.sheafInvariantFunctor R J).obj F = a.invariantPresheaf R F.obj :=
  rfl

/-- The presheaf of invariant sections is left exact on module sheaves. -/
instance sheafInvariantFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (a.sheafInvariantFunctor R J :
      Sheaf J (ModuleCat.{w} R) ⥤ (Eᵒᵖ ⥤ ModuleCat.{w} R)) :=
  comp_preservesFiniteLimits _ _

end Invariants

variable (J : GrothendieckTopology T)

/-- The presheaf of section representations of module sheaves. -/
def sheafSectionsRepFunctor : Sheaf J (ModuleCat.{w} R) ⥤ (Eᵒᵖ ⥤ Rep.{w} R K) :=
  sheafToPresheaf J (ModuleCat.{w} R) ⋙ a.sectionsRepFunctor R

/-- The presheaf of section representations is left exact on module sheaves. -/
instance sheafSectionsRepFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (a.sheafSectionsRepFunctor R J :
      Sheaf J (ModuleCat.{w} R) ⥤ (Eᵒᵖ ⥤ Rep.{w} R K)) :=
  comp_preservesFiniteLimits _ _

end NaturalAction

section Smooth

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {R : Type uR} [CommRing R]

/-- Let `b` be an action of `G` on `U` whose restriction to the open subgroup `G` is
admissible for `L`. Then the sections over `U` of a discrete module presheaf form a smooth
representation of `G`. -/
theorem isSmooth_actionRepresentation_of_isAdmissible_top (L : LocalActionSystem T G) {U : T}
    {b : G →* (End U)ᵐᵒᵖ}
    (hb : L.IsAdmissible U ⊤ (b.comp ((⊤ : OpenSubgroup G) : Subgroup G).subtype))
    {F : Tᵒᵖ ⥤ ModuleCat.{w} R} (hF : L.IsDiscrete F) :
    IsSmooth (actionRepresentation F b) := fun s => by
  obtain ⟨H, -, hH⟩ := hF U ⊤ _ hb s
  exact ⟨H, fun h => hH ⟨h, trivial⟩ h.2⟩

variable (R) (L : LocalActionSystem T G) (J : GrothendieckTopology T)

/-- Sections over `U` of discrete module sheaves, as smooth representations of `G`, for an
action `b` of `G` on `U` whose restriction to the open subgroup `G` is admissible. -/
def discreteSectionsSmoothOfTop {U : T} {b : G →* (End U)ᵐᵒᵖ}
    (hb : L.IsAdmissible U ⊤ (b.comp ((⊤ : OpenSubgroup G) : Subgroup G).subtype)) :
    L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ SmoothRep.{uR, uG, w} R G :=
  (smoothRepProperty R G).lift (discreteSectionsRep R L J b)
    (fun F => isSmooth_actionRepresentation_of_isAdmissible_top L hb F.property)

/-- The algebraic representation underlying the smooth sections. -/
def discreteSectionsSmoothOfTopToRepIso {U : T} {b : G →* (End U)ᵐᵒᵖ}
    (hb : L.IsAdmissible U ⊤ (b.comp ((⊤ : OpenSubgroup G) : Subgroup G).subtype)) :
    (discreteSectionsSmoothOfTop R L J hb :
      L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ SmoothRep.{uR, uG, w} R G) ⋙ SmoothRep.toRep ≅
      discreteSectionsRep R L J b :=
  ObjectProperty.liftCompιIso _ _ _

instance discreteSectionsSmoothOfTop_additive {U : T} {b : G →* (End U)ᵐᵒᵖ}
    (hb : L.IsAdmissible U ⊤ (b.comp ((⊤ : OpenSubgroup G) : Subgroup G).subtype)) :
    (discreteSectionsSmoothOfTop R L J hb :
      L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ SmoothRep.{uR, uG, w} R G).Additive where
  map_add := by
    intros
    rfl

variable [HasSheafify J (ModuleCat.{w} R)] [L.HasFiniteEquivariantRefinements J]

/-- The smooth sections are left exact. -/
instance discreteSectionsSmoothOfTop_preservesFiniteLimits {U : T} {b : G →* (End U)ᵐᵒᵖ}
    (hb : L.IsAdmissible U ⊤ (b.comp ((⊤ : OpenSubgroup G) : Subgroup G).subtype)) :
    PreservesFiniteLimits (discreteSectionsSmoothOfTop R L J hb :
      L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ SmoothRep.{uR, uG, w} R G) := by
  have : PreservesFiniteLimits ((discreteSectionsSmoothOfTop R L J hb :
      L.DiscreteSheaf (ModuleCat.{w} R) J ⥤ SmoothRep.{uR, uG, w} R G) ⋙ SmoothRep.toRep) :=
    preservesFiniteLimits_of_natIso (discreteSectionsSmoothOfTopToRepIso R L J hb).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ SmoothRep.toRep

end Smooth

end Langlands.Sheaf.Equivariant
