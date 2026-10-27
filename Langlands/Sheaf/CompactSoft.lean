import Langlands.Sheaf.CompactSupport
import Mathlib.Topology.Sheaves.Flasque
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
import Mathlib.Topology.Separation.Regular
import Mathlib.CategoryTheory.Retract

/-!
# Sections over subsets and `c`-soft module sheaves

For a subset `K` of a topological space, `setSections F K` is the colimit of the
sections of `F` over the open neighbourhoods of `K`. A module sheaf is `c`-soft
when, for every compact `K`, every element of this colimit is the germ along `K` of
a global section with compact support. Flasque sheaves on locally compact regular
spaces are `c`-soft.
-/

noncomputable section

namespace Langlands.Sheaf.CompactSoft

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}}

/-- The open neighbourhoods of a subset `K`, ordered by inclusion. -/
def SetNhds (K : Set X) : Type u := {U : Opens X // K ⊆ U}

namespace SetNhds

variable {K : Set X}

instance : PartialOrder (SetNhds K) :=
  inferInstanceAs (PartialOrder {U : Opens X // K ⊆ U})

theorem le_def (U V : SetNhds K) : U ≤ V ↔ U.1 ≤ V.1 := Iff.rfl

instance : SemilatticeInf (SetNhds K) where
  inf U V := ⟨U.1 ⊓ V.1, fun _ hx => ⟨U.2 hx, V.2 hx⟩⟩
  inf_le_left U V := @inf_le_left _ _ U.1 V.1
  inf_le_right U V := @inf_le_right _ _ U.1 V.1
  le_inf U V W h₁ h₂ := @le_inf _ _ U.1 V.1 W.1 h₁ h₂

instance : OrderTop (SetNhds K) where
  top := ⟨⊤, fun _ _ => trivial⟩
  le_top U := le_top (a := U.1)

instance : Nonempty (SetNhds K) := ⟨⊤⟩

variable (K) in
/-- The inclusion of the neighbourhoods of `K` into all open sets. -/
def inclusion : SetNhds K ⥤ Opens X :=
  (Subtype.mono_coe _).functor

@[simp]
theorem inclusion_obj (U : Opens X) (h : K ⊆ U) : (inclusion K).obj ⟨U, h⟩ = U :=
  rfl

/-- Neighbourhoods of a larger set are neighbourhoods of a smaller one. -/
def map {L : Set X} (h : K ⊆ L) : SetNhds L ⥤ SetNhds K :=
  Monotone.functor (f := fun U => (⟨U.1, h.trans U.2⟩ : SetNhds K)) fun _ _ hUV => hUV

/-- The neighbourhood `U` of the open set `U` itself is the least one. -/
def isTerminalSelf (U : Opens X) :
    IsTerminal (op (⟨U, subset_rfl⟩ : SetNhds (U : Set X))) :=
  IsTerminal.ofUniqueHom (fun V => (homOfLE (show (⟨U, subset_rfl⟩ : SetNhds (U : Set X)) ≤
      unop V from (unop V).2)).op)
    fun _ _ => Subsingleton.elim _ _

end SetNhds

variable {R : Type u} [CommRing R]

variable (R) in
/-- The colimit of sections over the open neighbourhoods of `K`, as a functor of the
presheaf. -/
def setSectionsFunctor (K : Set X) : X.Presheaf (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  (Functor.whiskeringLeft _ _ (ModuleCat.{u} R)).obj (SetNhds.inclusion K).op ⋙ colim

/-- Godement's sections over a subset `K`: the colimit of `F(U)` over open `U ⊇ K`. -/
abbrev setSections (F : X.Presheaf (ModuleCat.{u} R)) (K : Set X) : ModuleCat.{u} R :=
  (setSectionsFunctor R K).obj F

/-- The germ along `K` of a section over an open neighbourhood `U` of `K`. -/
def setGerm (F : X.Presheaf (ModuleCat.{u} R)) {K : Set X} (U : Opens X) (hKU : K ⊆ U) :
    F.obj (op U) ⟶ setSections F K :=
  colimit.ι ((SetNhds.inclusion K).op ⋙ F) (op ⟨U, hKU⟩)

/-- Germs along `K` are compatible with restriction between neighbourhoods. -/
@[reassoc]
theorem setGerm_res (F : X.Presheaf (ModuleCat.{u} R)) {K : Set X} {U V : Opens X}
    (i : U ⟶ V) (hKU : K ⊆ U) :
    F.map i.op ≫ setGerm F U hKU = setGerm F V (hKU.trans i.le) :=
  let i' : (⟨U, hKU⟩ : SetNhds K) ⟶ ⟨V, hKU.trans i.le⟩ := i
  colimit.w ((SetNhds.inclusion K).op ⋙ F) i'.op

theorem setGerm_res_apply (F : X.Presheaf (ModuleCat.{u} R)) {K : Set X} {U V : Opens X}
    (i : U ⟶ V) (hKU : K ⊆ U) (s : F.obj (op V)) :
    setGerm F U hKU (F.map i.op s) = setGerm F V (hKU.trans i.le) s := by
  rw [← setGerm_res F i hKU]
  rfl

/-- Every element of `setSections F K` is the germ of a section over a neighbourhood. -/
theorem exists_setGerm_eq (F : X.Presheaf (ModuleCat.{u} R)) {K : Set X}
    (t : setSections F K) :
    ∃ (U : Opens X) (hKU : K ⊆ U) (s : F.obj (op U)), setGerm F U hKU s = t := by
  obtain ⟨U, s, e⟩ :=
    Types.jointly_surjective.{u, u} _
      (isColimitOfPreserves (forget (ModuleCat.{u} R)) (colimit.isColimit _)) t
  revert s e
  induction U with | op U => ?_
  obtain ⟨V, m⟩ := U
  intro s e
  exact ⟨V, m, s, e⟩

/-- Two sections with the same germ along `K` agree on a smaller neighbourhood of `K`. -/
theorem setGerm_eq (F : X.Presheaf (ModuleCat.{u} R)) {K : Set X} {U V : Opens X}
    (hKU : K ⊆ U) (hKV : K ⊆ V) (s : F.obj (op U)) (t : F.obj (op V))
    (h : setGerm F U hKU s = setGerm F V hKV t) :
    ∃ (W : Opens X) (_ : K ⊆ W) (iU : W ⟶ U) (iV : W ⟶ V),
      F.map iU.op s = F.map iV.op t := by
  obtain ⟨W, iU, iV, e⟩ :=
    (colimit.isColimit ((SetNhds.inclusion K).op ⋙ F)).eq_iff.mp h
  exact ⟨(unop W).1, (unop W).2, iU.unop, iV.unop, e⟩

/-- Sections that agree on a neighbourhood of `K` have the same germ along `K`. -/
theorem setGerm_ext (F : X.Presheaf (ModuleCat.{u} R)) {K : Set X} {U V W : Opens X}
    (hKU : K ⊆ U) (hKV : K ⊆ V) (hKW : K ⊆ W) (iU : W ⟶ U) (iV : W ⟶ V)
    {s : F.obj (op U)} {t : F.obj (op V)} (h : F.map iU.op s = F.map iV.op t) :
    setGerm F U hKU s = setGerm F V hKV t := by
  rw [← setGerm_res_apply F iU hKW, ← setGerm_res_apply F iV hKW, h]

/-- Germs along `K` are natural in the presheaf. -/
@[reassoc]
theorem setGerm_naturality {F G : X.Presheaf (ModuleCat.{u} R)} (f : F ⟶ G) {K : Set X}
    (U : Opens X) (hKU : K ⊆ U) :
    f.app (op U) ≫ setGerm G U hKU = setGerm F U hKU ≫ (setSectionsFunctor R K).map f :=
  (ι_colimMap (Functor.whiskerLeft (SetNhds.inclusion K).op f) (op ⟨U, hKU⟩)).symm

/-- Maps out of `setSections F K` are determined by their composites with the germs. -/
theorem setSections_hom_ext {F : X.Presheaf (ModuleCat.{u} R)} {K : Set X}
    {M : ModuleCat.{u} R} {f g : setSections F K ⟶ M}
    (h : ∀ (U : Opens X) (hKU : K ⊆ U), setGerm F U hKU ≫ f = setGerm F U hKU ≫ g) :
    f = g :=
  colimit.hom_ext fun U => h (unop U).1 (unop U).2

/-- Restriction from germs along `L` to germs along a subset `K`. -/
def setSectionsRes (F : X.Presheaf (ModuleCat.{u} R)) {K L : Set X} (h : K ⊆ L) :
    setSections F L ⟶ setSections F K :=
  colimit.pre ((SetNhds.inclusion K).op ⋙ F) (SetNhds.map h).op

/-- Restriction of germs sends the germ along `L` to the germ along `K`. -/
@[reassoc (attr := simp)]
theorem setGerm_setSectionsRes (F : X.Presheaf (ModuleCat.{u} R)) {K L : Set X}
    (h : K ⊆ L) (U : Opens X) (hLU : L ⊆ U) :
    setGerm F U hLU ≫ setSectionsRes F h = setGerm F U (h.trans hLU) :=
  colimit.ι_pre ((SetNhds.inclusion K).op ⋙ F) (SetNhds.map h).op (op ⟨U, hLU⟩)

theorem setSectionsRes_id (F : X.Presheaf (ModuleCat.{u} R)) (K : Set X) :
    setSectionsRes F (subset_refl K) = 𝟙 _ :=
  setSections_hom_ext fun U hKU => by
    rw [setGerm_setSectionsRes, Category.comp_id]

theorem setSectionsRes_comp (F : X.Presheaf (ModuleCat.{u} R)) {K L M : Set X}
    (hKL : K ⊆ L) (hLM : L ⊆ M) :
    setSectionsRes F hLM ≫ setSectionsRes F hKL = setSectionsRes F (hKL.trans hLM) :=
  setSections_hom_ext fun U hMU => by
    rw [setGerm_setSectionsRes_assoc, setGerm_setSectionsRes, setGerm_setSectionsRes]

/-- Restriction of germs is natural in the presheaf. -/
@[reassoc]
theorem setSectionsRes_naturality {F G : X.Presheaf (ModuleCat.{u} R)} (f : F ⟶ G)
    {K L : Set X} (h : K ⊆ L) :
    (setSectionsFunctor R L).map f ≫ setSectionsRes G h =
      setSectionsRes F h ≫ (setSectionsFunctor R K).map f :=
  setSections_hom_ext fun U hLU => by
    rw [← setGerm_naturality_assoc, setGerm_setSectionsRes, setGerm_setSectionsRes_assoc,
      setGerm_naturality]

/-- Over an open set, the germ of a section over that set is an isomorphism. -/
instance isIso_setGerm_self (F : X.Presheaf (ModuleCat.{u} R)) (U : Opens X) :
    IsIso (setGerm F U (subset_refl (U : Set X))) :=
  IsColimit.isIso_ι_app_of_isTerminal (colimit.isColimit _) _ (SetNhds.isTerminalSelf U)

/-- Over an open set, Godement's sections are the ordinary sections. -/
def openSectionsIso (F : X.Presheaf (ModuleCat.{u} R)) (U : Opens X) :
    setSections F (U : Set X) ≅ F.obj (op U) :=
  (asIso (setGerm F U (subset_refl (U : Set X)))).symm

/-- The germ along `K` of a compactly supported global section. -/
def compactGerm (F : X.Presheaf (ModuleCat.{u} R)) (K : Set X) :
    CompactSupport.presheafFunctor.obj F ⟶ setSections F K :=
  ModuleCat.ofHom (CompactSupport.submodule F).subtype ≫
    setGerm F ⊤ (Set.subset_univ K)

theorem compactGerm_apply (F : X.Presheaf (ModuleCat.{u} R)) (K : Set X)
    (s : CompactSupport.presheafFunctor.obj F) :
    compactGerm F K s = setGerm F ⊤ (Set.subset_univ K) s.1 :=
  rfl

/-- Germs of compactly supported sections are natural in the presheaf. -/
@[reassoc]
theorem compactGerm_naturality {F G : X.Presheaf (ModuleCat.{u} R)} (f : F ⟶ G)
    (K : Set X) :
    CompactSupport.presheafFunctor.map f ≫ compactGerm G K =
      compactGerm F K ≫ (setSectionsFunctor R K).map f := by
  ext s
  change setGerm G ⊤ (Set.subset_univ K) (f.app (op ⊤) s.1) =
    (setSectionsFunctor R K).map f (setGerm F ⊤ (Set.subset_univ K) s.1)
  exact congrArg (fun φ => φ s.1) (setGerm_naturality f ⊤ (Set.subset_univ K))

/-- A module sheaf is `c`-soft if every germ along a compact set is the germ of a
compactly supported global section. This is the colimit form of Grothendieck's
`Φ`-softness (Tohoku, p.159) for `Φ` the compact sets; on locally compact Hausdorff
spaces the two agree (not formalized here). -/
def IsCSoft (F : TopCat.Sheaf (ModuleCat.{u} R) X) : Prop :=
  ∀ K : Set X, IsCompact K → Function.Surjective (compactGerm F.presheaf K)

/-- `c`-softness unfolded: germs along compact sets lift to global sections whose
support is compact. -/
theorem isCSoft_iff (F : TopCat.Sheaf (ModuleCat.{u} R) X) :
    IsCSoft F ↔ ∀ K : Set X, IsCompact K → ∀ t : setSections F.presheaf K,
      ∃ s : F.presheaf.obj (op ⊤), IsCompact (CompactSupport.support F.presheaf s) ∧
        setGerm F.presheaf ⊤ (Set.subset_univ K) s = t := by
  refine forall_congr' fun K => forall_congr' fun _ => forall_congr' fun t => ?_
  exact ⟨fun ⟨s, hs⟩ => ⟨s.1, s.2, hs⟩, fun ⟨s, hc, hs⟩ => ⟨⟨s, hc⟩, hs⟩⟩

/-- A retract of a `c`-soft sheaf is `c`-soft. -/
theorem IsCSoft.of_retract {F G : TopCat.Sheaf (ModuleCat.{u} R) X} (h : Retract G F)
    (hF : IsCSoft F) : IsCSoft G := by
  intro K hK t
  obtain ⟨s, hs⟩ := hF K hK ((setSectionsFunctor R K).map h.i.hom t)
  refine ⟨CompactSupport.presheafFunctor.map h.r.hom s, ?_⟩
  have e := congrArg (fun φ => φ s) (compactGerm_naturality h.r.hom K)
  change compactGerm G.presheaf K (CompactSupport.presheafFunctor.map h.r.hom s) =
    (setSectionsFunctor R K).map h.r.hom (compactGerm F.presheaf K s) at e
  rw [e, hs]
  change ((setSectionsFunctor R K).map h.i.hom ≫ (setSectionsFunctor R K).map h.r.hom) t = t
  rw [← Functor.map_comp]
  have hir : h.i.hom ≫ h.r.hom = 𝟙 G.presheaf := congrArg (fun φ => φ.hom) h.retract
  rw [hir, CategoryTheory.Functor.map_id]
  rfl

/-- `c`-softness is invariant under isomorphism. -/
theorem IsCSoft.of_iso {F G : TopCat.Sheaf (ModuleCat.{u} R) X} (e : F ≅ G)
    (hF : IsCSoft F) : IsCSoft G :=
  hF.of_retract ⟨e.inv, e.hom, e.inv_hom_id⟩

/-- On disjoint open sets, a section over the first set and the zero section over the
second glue to a section over their union. -/
theorem exists_glue_zero (F : TopCat.Sheaf (ModuleCat.{u} R) X) {V W : Opens X}
    (h : V ⊓ W = ⊥) (s : F.presheaf.obj (op V)) :
    ∃ g : F.presheaf.obj (op (V ⊔ W)),
      F.presheaf.map (homOfLE le_sup_left : V ⟶ V ⊔ W).op g = s ∧
        F.presheaf.map (homOfLE le_sup_right : W ⟶ V ⊔ W).op g = 0 := by
  obtain ⟨l, hl₁, hl₂⟩ := BinaryFan.IsLimit.lift' (F.isProductOfDisjoint V W h)
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ s)) 0
  refine ⟨l (1 : R), ?_, ?_⟩
  · have := congrArg (fun φ => φ (1 : R)) hl₁
    simpa using this
  · have := congrArg (fun φ => φ (1 : R)) hl₂
    simpa using this

/-- A flasque module sheaf on a locally compact regular space is `c`-soft
(Grothendieck, Tohoku, p.159, and the proof of Lemma 3.7.1 2) on pp.172-173 with `f` the
identity). -/
theorem isCSoft_of_isFlasque [LocallyCompactSpace X] [RegularSpace X]
    (F : TopCat.Sheaf (ModuleCat.{u} R) X) [F.IsFlasque] : IsCSoft F := by
  rw [isCSoft_iff]
  intro K hK t
  obtain ⟨U, hKU, s, rfl⟩ := exists_setGerm_eq F.presheaf t
  obtain ⟨V, hV, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK U.isOpen hKU
  let V' : Opens X := ⟨V, hV⟩
  let W : Opens X := ⟨(closure V)ᶜ, isClosed_closure.isOpen_compl⟩
  have hVW : V' ⊓ W = ⊥ := by
    ext x
    simp only [Opens.coe_inf, Opens.coe_bot, Set.mem_inter_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    exact fun hx hx' => hx' (subset_closure hx)
  let iVU : V' ⟶ U := homOfLE (subset_closure.trans hVU)
  obtain ⟨g, hg₁, hg₂⟩ := exists_glue_zero F hVW (F.presheaf.map iVU.op s)
  obtain ⟨g', hg'⟩ := (ModuleCat.epi_iff_surjective
    (F.presheaf.map (homOfLE le_top : V' ⊔ W ⟶ ⊤).op)).mp inferInstance g
  refine ⟨g', ?_, ?_⟩
  · refine hVc.of_isClosed_subset (CompactSupport.isClosed_support _ _) ?_
    intro x hx
    by_contra hxV
    apply hx
    have hW : F.presheaf.map (homOfLE le_top : W ⟶ ⊤).op g' = 0 := by
      rw [← hg₂, ← hg', ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
      rfl
    change F.presheaf.Γgerm x g' = 0
    rw [← F.presheaf.Γgerm_res_apply (U := W) x hxV g' (i := homOfLE le_top), hW, map_zero]
  · refine setGerm_ext F.presheaf _ _ hKV (homOfLE le_top : V' ⟶ ⊤) iVU ?_
    rw [← hg₁, ← hg', ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
    rfl

end Langlands.Sheaf.CompactSoft
