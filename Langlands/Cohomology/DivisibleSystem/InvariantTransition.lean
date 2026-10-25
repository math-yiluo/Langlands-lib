import Langlands.Cohomology.DivisibleSystem.StandardMap
import Langlands.Cohomology.DivisibleSystem.InvariantComparison

/-!
# Transition maps between Harris's `C_m^{•,H}` for a change of `H`

Harris 1999, §2, p.306, replaces `H` by a smaller subgroup `H'`, normal in `S(ẽ)`, states a
natural isomorphism `C_m^{•,H} = [C_m^{•,H'}]^H`, and then takes the direct limit as `H` shrinks.
This module does not formalize that isomorphism. It builds the transition morphisms such a
direct limit uses, and proves that they are compatible with the comparisons of the
InvariantComparison module.

For an `ℓ`-divisible system `K` of `ℕ`-graded complexes of smooth representations of `G` and
normal subgroups `H' ≤ H` of finite index with `|ker (G ⧸ H' → G ⧸ H)|` invertible in `R`, the
transition morphism `quotientInvariantsTransition` goes from the inflation to `G` of
`C_m^{•,H}` (`quotientInvariantsTotalSystem`) to the inflation of `C_m^{•,H'}`. It is the
normalized fiber sum `groupStandardTotalSystemMap` of the StandardMap module along
`G ⧸ H' ⟶ G ⧸ H`, followed by the map of standard total complexes induced by the inclusion of
the `H`-invariants into the `H'`-invariants. Followed by the comparison
`quotientInvariantsTotalSystemToRepExtend` for `H'`, it is the comparison for `H`
(`quotientInvariantsTransition_comp_toRepExtend`). So, given Worker 3's unproved
`ProPInvariantSubcomplexStatement`, it is a quasi-isomorphism at every level at which `H` acts
trivially on the cohomology, for `H`, `H'` pro-`p` and `p` invertible in `R`.

Transitivity in `H`, the direct limit over `H` and Harris's (2.6) are not constructed.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w uR uG uV u v u₁ v₁ u₂ v₂ u₃ v₃

section ExtendComp

open HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : c.Embedding c')
  {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D] [HasZeroObject D]
  {E : Type u₃} [Category.{v₃} E] [HasZeroMorphisms E] [HasZeroObject E]
  {F₁ : C ⥤ D} {F₂ : D ⥤ E} {F₃ : C ⥤ E} [F₁.PreservesZeroMorphisms]
  [F₂.PreservesZeroMorphisms] [F₃.PreservesZeroMorphisms] (α : F₁ ⋙ F₂ ≅ F₃)
  (K : HomologicalComplex C c)

lemma extendXMapIso_inv_comp_comp (j : Option ι) :
    α.inv.app (extend.X K j) ≫ F₂.map (DerivedPlus.extendXMapIso F₁ K j).inv ≫
        (DerivedPlus.extendXMapIso F₂ ((F₁.mapHomologicalComplex c).obj K) j).inv =
      (DerivedPlus.extendXMapIso F₃ K j).inv ≫
        extend.mapX ((Functor.mapHomologicalComplexCompIso α c).inv.app K) j :=
  match j with
  | none => (extend.isZero_X _ rfl).eq_of_tgt _ _
  | some _ => (congrArg (α.inv.app _ ≫ ·) ((Category.comp_id _).trans (F₂.map_id _))).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The comparisons `extendMapIso` for `F₁`, `F₂` and `F₃ ≅ F₁ ⋙ F₂` are compatible. -/
lemma extendMapIso_hom_comp :
    (Functor.mapHomologicalComplexCompIso α c').inv.app (K.extend e) ≫
        (F₂.mapHomologicalComplex c').map (extendMapIso e F₁ K).hom ≫
          (extendMapIso e F₂ ((F₁.mapHomologicalComplex c).obj K)).hom =
      (extendMapIso e F₃ K).hom ≫
        extendMap ((Functor.mapHomologicalComplexCompIso α c).inv.app K) e := by
  ext i'
  exact extendXMapIso_inv_comp_comp α K (e.r i')

variable {e α} in
/-- A compatibility of comparisons with extensions along `e`: given `t : T ⟶ X.extend e`,
`t₁ : T₁ ⟶ (F₁ X).extend e` and `t₂ : T₂ ⟶ X'.extend e` with `g : F₁ T ⟶ T₁` and `s : T₁ ⟶ T₂`
compatible with `t`, `t₁`, `t₂` and `c₀ : F₁ X ⟶ X'`, and `u' : F₂ X' ⟶ Y`, `u : F₃ X ⟶ Y` with
`α.inv ≫ F₂ c₀ ≫ u' = u`, the morphism `α.inv ≫ F₂ (g ≫ s)` followed by the comparison built from
`t₂` and `u'` is the comparison built from `t` and `u`. -/
lemma extendComparison_comp_eq {T : HomologicalComplex C c'} {X : HomologicalComplex C c}
    {T₁ T₂ : HomologicalComplex D c'} {X' : HomologicalComplex D c} {Y : HomologicalComplex E c}
    (t : T ⟶ X.extend e) (g : (F₁.mapHomologicalComplex c').obj T ⟶ T₁)
    (t₁ : T₁ ⟶ ((F₁.mapHomologicalComplex c).obj X).extend e) (s : T₁ ⟶ T₂)
    (t₂ : T₂ ⟶ X'.extend e) (c₀ : (F₁.mapHomologicalComplex c).obj X ⟶ X')
    (u' : (F₂.mapHomologicalComplex c).obj X' ⟶ Y) (u : (F₃.mapHomologicalComplex c).obj X ⟶ Y)
    (h₁ : g ≫ t₁ = (F₁.mapHomologicalComplex c').map t ≫ (extendMapIso e F₁ X).hom)
    (h₂ : s ≫ t₂ = t₁ ≫ extendMap c₀ e)
    (h₃ : (Functor.mapHomologicalComplexCompIso α c).inv.app X ≫
      (F₂.mapHomologicalComplex c).map c₀ ≫ u' = u) :
    ((Functor.mapHomologicalComplexCompIso α c').inv.app T ≫
        (F₂.mapHomologicalComplex c').map (g ≫ s)) ≫
      (F₂.mapHomologicalComplex c').map t₂ ≫ (extendMapIso e F₂ X').hom ≫ extendMap u' e =
    (F₃.mapHomologicalComplex c').map t ≫ (extendMapIso e F₃ X).hom ≫ extendMap u e := by
  have h₄ : (g ≫ s) ≫ t₂ = (F₁.mapHomologicalComplex c').map t ≫ (extendMapIso e F₁ X).hom ≫
      extendMap c₀ e := by
    rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]
  have hn : (Functor.mapHomologicalComplexCompIso α c').inv.app T ≫
      (F₂.mapHomologicalComplex c').map ((F₁.mapHomologicalComplex c').map t) =
      (F₃.mapHomologicalComplex c').map t ≫
        (Functor.mapHomologicalComplexCompIso α c').inv.app (X.extend e) :=
    ((Functor.mapHomologicalComplexCompIso α c').inv.naturality t).symm
  rw [Category.assoc, ← Category.assoc ((F₂.mapHomologicalComplex c').map (g ≫ s)),
    ← Functor.map_comp, h₄, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    reassoc_of% hn, reassoc_of% (extendMapIso_hom_naturality e F₂ c₀),
    reassoc_of% (extendMapIso_hom_comp e α X), ← extendMap_comp, ← extendMap_comp, h₃]

end ExtendComp

section QuotientChange

variable (R : Type uR) [CommRing R] {G : Type uG} [Group G] {H H' : Subgroup G} [H.Normal]
  [H'.Normal] (hHH' : H' ≤ H)

/-- The projection `G ⧸ H' ⟶ G ⧸ H` for normal subgroups `H' ≤ H`. -/
abbrev quotientProjection : G ⧸ H' →* G ⧸ H :=
  QuotientGroup.map H' H (MonoidHom.id G) hHH'

lemma quotientProjection_mk (g : G) :
    quotientProjection hHH' (g : G ⧸ H') = (g : G ⧸ H) :=
  rfl

lemma surjective_quotientProjection : Function.Surjective (quotientProjection hHH') :=
  fun q => QuotientGroup.induction_on q fun g => ⟨(g : G ⧸ H'), rfl⟩

/-- The inclusion of the `H`-invariants into the `H'`-invariants, `G ⧸ H'`-equivariant when
`G ⧸ H'` acts on the `H`-invariants through `G ⧸ H' ⟶ G ⧸ H`. -/
def quotientInvariantsChange :
    Rep.quotientToInvariantsFunctor.{uV} R H ⋙ Rep.resFunctor (quotientProjection hHH') ⟶
      Rep.quotientToInvariantsFunctor.{uV} R H' where
  app A := Rep.ofHom ⟨Submodule.inclusion fun x hx h => hx ⟨h, hHH' h.2⟩,
    fun g => QuotientGroup.induction_on g fun _ => LinearMap.ext fun _ => Subtype.ext rfl⟩
  naturality _ _ _ := by
    ext
    rfl

/-- Inflation along `G ⟶ G ⧸ H` is inflation along `G ⧸ H' ⟶ G ⧸ H` followed by inflation along
`G ⟶ G ⧸ H'`; the components are identities. -/
def quotientInflationResIso :
    Rep.resFunctor (quotientProjection hHH') ⋙ Rep.quotientInflation.{uR, uG, uV} R H' ≅
      Rep.quotientInflation.{uR, uG, uV} R H :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

end QuotientChange

section SmoothChange

variable (R : Type uR) [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  {H H' : Subgroup G} [H.Normal] [H'.Normal] (hHH' : H' ≤ H)

/-- `quotientInvariantsChange` on the underlying representations of smooth representations. -/
abbrev smoothQuotientInvariantsChange :
    smoothQuotientInvariants.{uR, uG, uV} R H ⋙ Rep.resFunctor (quotientProjection hHH') ⟶
      smoothQuotientInvariants.{uR, uG, uV} R H' :=
  Functor.whiskerLeft SmoothRep.toRep (quotientInvariantsChange.{uR, uG, uV} R hHH')

end SmoothChange

namespace DivisibleSystem

section MapComp

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] {ℓ : ℕ}
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {F₃ : A ⥤ E} [F₁.Additive] [PreservesFiniteLimits F₁]
  [PreservesFiniteColimits F₁] [F₂.Additive] [PreservesFiniteLimits F₂]
  [PreservesFiniteColimits F₂] [F₃.Additive] [PreservesFiniteLimits F₃]
  [PreservesFiniteColimits F₃]

/-- For `α : F₁ ⋙ F₂ ≅ F₃`, the comparison `T.map F₃ ⟶ (T.map F₁).map F₂` given by `α.inv`. -/
def mapCompHom (α : F₁ ⋙ F₂ ≅ F₃) (T : DivisibleSystem A ℓ) : T.map F₃ ⟶ (T.map F₁).map F₂ :=
  ⟨Functor.whiskerLeft T.tower α.inv, fun h => α.inv.naturality (T.inclusion h)⟩

lemma mapCompHom_tower_app (α : F₁ ⋙ F₂ ≅ F₃) (T : DivisibleSystem A ℓ) (m : ℕᵒᵖ) :
    (mapCompHom α T).tower.app m = α.inv.app (T.tower.obj m) :=
  rfl

end MapComp

section MapComplexesComp

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] {ℓ : ℕ} (K : DivisibleSystem (CochainComplex C ℕ) ℓ)
  {Φ : C ⥤ D} {Ψ : D ⥤ E} {Φ' : C ⥤ E} [Φ.Additive] [PreservesFiniteLimits Φ] [Ψ.Additive]
  [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ] [Φ'.Additive] [PreservesFiniteLimits Φ']

/-- For `β : Φ ⋙ Ψ ⟶ Φ'`, the morphism from `Ψ` applied degreewise to `K.mapComplexes Φ` to
`K.mapComplexes Φ'`: `β` in every degree. -/
def mapComplexesCompHom (β : Φ ⋙ Ψ ⟶ Φ')
    (hΦ : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ), Epi (Φ.map ((K.projection h).f q)))
    (hΦ' : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ), Epi (Φ'.map ((K.projection h).f q))) :
    (K.mapComplexes Φ hΦ).map (Ψ.mapHomologicalComplex (ComplexShape.up ℕ)) ⟶
      K.mapComplexes Φ' hΦ' :=
  ⟨Functor.whiskerLeft K.tower ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (Φ ⋙ Ψ)) _).hom ≫ NatTrans.mapHomologicalComplex β _),
    fun h => ((Functor.mapHomologicalComplexCompIso (Iso.refl (Φ ⋙ Ψ)) _).hom ≫
      NatTrans.mapHomologicalComplex β _).naturality (K.inclusion h)⟩

end MapComplexesComp

section StandardTotalMap

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {ℓ : ℕ} (N : ℕ) (P : A ⥤ A)
  (ε : P ⟶ 𝟭 A) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- The morphism of the total complexes (rows `q < N`) of the standard resolutions along `P`
induced by a morphism of `ℓ`-divisible systems of `ℕ`-graded complexes. -/
abbrev standardTotalSystemMapOfHom {K K' : DivisibleSystem (CochainComplex A ℕ) ℓ}
    (f : K ⟶ K') : K.standardTotalSystem N P ε ⟶ K'.standardTotalSystem N P ε :=
  totalSystemMap N ((mapFunctor _ ℓ ((standardResolution P ε).mapHomologicalComplex
    (ComplexShape.up ℕ))).map f)

/-- `standardTotalSystemToExtend` is natural in the system. -/
lemma standardTotalSystemMapOfHom_comp_toExtend {K K' : DivisibleSystem (CochainComplex A ℕ) ℓ}
    (f : K ⟶ K') (hK : ∀ m q, N ≤ q → IsZero ((K.obj m).X q))
    (hK' : ∀ m q, N ≤ q → IsZero ((K'.obj m).X q)) :
    standardTotalSystemMapOfHom N P ε f ≫ K'.standardTotalSystemToExtend N P ε hK' =
      K.standardTotalSystemToExtend N P ε hK ≫
        (mapFunctor _ ℓ (ComplexShape.embeddingUpNat.extendFunctor A)).map f := by
  refine hom_ext (NatTrans.ext (funext fun m => HomologicalComplex.hom_ext _ _ fun n => ?_))
  have h₁ := (NatTrans.mapHomologicalComplex (standardResolutionAugmentation P ε)
    (ComplexShape.up ℕ)).naturality (f.tower.app m)
  have h₂ : ((upFinTotalFunctor A N).map
        (((standardResolution P ε).mapHomologicalComplex (ComplexShape.up ℕ)).map (f.tower.app m) ≫
          (NatTrans.mapHomologicalComplex (standardResolutionAugmentation P ε)
            (ComplexShape.up ℕ)).app (K'.tower.obj m))).f n =
      ((upFinTotalFunctor A N).map
        ((NatTrans.mapHomologicalComplex (standardResolutionAugmentation P ε)
            (ComplexShape.up ℕ)).app (K.tower.obj m) ≫
          ((ChainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℕ)).map
            (f.tower.app m))).f n :=
    congrArg (fun φ => ((upFinTotalFunctor A N).map φ).f n) h₁
  have h₃ := columnComparisonF_naturality N (f.tower.app m) n
  rw [Functor.map_comp, Functor.map_comp, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f] at h₂
  change ((upFinTotalFunctor A N).map
        (((standardResolution P ε).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (f.tower.app m))).f n ≫
      ((upFinTotalFunctor A N).map ((NatTrans.mapHomologicalComplex
          (standardResolutionAugmentation P ε) (ComplexShape.up ℕ)).app (K'.tower.obj m))).f n ≫
        columnComparisonF N (K'.tower.obj m) n =
    (((upFinTotalFunctor A N).map ((NatTrans.mapHomologicalComplex
          (standardResolutionAugmentation P ε) (ComplexShape.up ℕ)).app (K.tower.obj m))).f n ≫
        columnComparisonF N (K.tower.obj m) n) ≫
      (HomologicalComplex.extendMap (f.tower.app m) ComplexShape.embeddingUpNat).f n
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ columnComparisonF N (K'.tower.obj m) n) h₂).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (_ ≫ ·) h₃

end StandardTotalMap

section Transition

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {ℓ : ℕ}
  (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℕ) ℓ)
  {H H' : Subgroup G} [H.Normal] [H'.Normal] (hHH' : H' ≤ H)

/-- The inclusion of the `H`-invariants into the `H'`-invariants, as a morphism from the
`H`-invariants system, restricted along `G ⧸ H' ⟶ G ⧸ H`, to the `H'`-invariants system. -/
def quotientInvariantsComplexesChange
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (hK' : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H').map ((K.projection h).f q))) :
    (K.quotientInvariantsComplexes H hK).map
        ((Rep.resFunctor.{max w uR uG} (k := R) (quotientProjection hHH')).mapHomologicalComplex
          (ComplexShape.up ℕ)) ⟶
      K.quotientInvariantsComplexes H' hK' :=
  K.mapComplexesCompHom (smoothQuotientInvariantsChange.{uR, uG, max w uR uG} R hHH') hK hK'

/-- After inflation to `G`, the inclusion of the `H`-invariants into the `H'`-invariants followed
by the inclusion of the `H'`-invariants is the inclusion of the `H`-invariants. -/
lemma quotientInvariantsComplexesChange_comp_inclusion
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (hK' : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H').map ((K.projection h).f q))) :
    mapCompHom (Functor.mapHomologicalComplexCompIso
        (quotientInflationResIso.{uR, uG, max w uR uG} R hHH') (ComplexShape.up ℕ))
        (K.quotientInvariantsComplexes H hK) ≫
      mapHom ((Rep.quotientInflation.{uR, uG, max w uR uG} R H').mapHomologicalComplex
          (ComplexShape.up ℕ)) (quotientInvariantsComplexesChange.{w, uR, uG} K hHH' hK hK') ≫
        inflateQuotientInvariantsComplexesHom.{w, uR, uG} K H' hK' ≫
          K.quotientInvariantsComplexesInclusion H' hK' =
    inflateQuotientInvariantsComplexesHom.{w, uR, uG} K H hK ≫
      K.quotientInvariantsComplexesInclusion H hK := by
  refine hom_ext (NatTrans.ext (funext fun m => HomologicalComplex.hom_ext _ _ fun q => ?_))
  ext x
  rfl

variable [H.FiniteIndex] [H'.FiniteIndex] [Fintype (G ⧸ H')] [DecidableEq (G ⧸ H)] (N : ℕ)

/-- The transition morphism from the inflated `C_m^{•,H}` to the inflated `C_m^{•,H'}` for normal
subgroups `H' ≤ H` of finite index with `|H/H'|` invertible in `R`: the normalized fiber sum
`groupStandardTotalSystemMap` along `G ⧸ H' ⟶ G ⧸ H`, followed by the map of standard total
complexes induced by the inclusion of the `H`-invariants into the `H'`-invariants. -/
def quotientInvariantsTransition
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (hK' : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H').map ((K.projection h).f q)))
    (hk : IsUnit (Nat.card (quotientProjection hHH').ker : R)) :
    inflatedQuotientInvariantsTotalSystem.{w, uR, uG} N K H hK ⟶
      inflatedQuotientInvariantsTotalSystem.{w, uR, uG} N K H' hK' :=
  mapCompHom (Functor.mapHomologicalComplexCompIso
      (quotientInflationResIso.{uR, uG, max w uR uG} R hHH') (ComplexShape.up ℤ))
      (quotientInvariantsTotalSystem.{w, uR, uG} N K H hK) ≫
    mapHom ((Rep.quotientInflation.{uR, uG, max w uR uG} R H').mapHomologicalComplex
        (ComplexShape.up ℤ))
      (groupStandardTotalSystemMap.{w, uG, uR} (quotientProjection hHH')
          (surjective_quotientProjection hHH') hk N (K.quotientInvariantsComplexes H hK) ≫
        standardTotalSystemMapOfHom N (indResBot.{w, uG, uR} R (G ⧸ H'))
          (indResBotCounit.{w, uG, uR} R (G ⧸ H'))
          (quotientInvariantsComplexesChange.{w, uR, uG} K hHH' hK hK'))

/-- The transition morphism is compatible with the comparisons
`quotientInvariantsTotalSystemToRepExtend` to the underlying complexes of representations of `K`
extended to `ℤ`, for `K` vanishing in degrees `q ≥ N`. -/
theorem quotientInvariantsTransition_comp_toRepExtend
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (hK' : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H').map ((K.projection h).f q)))
    (hk : IsUnit (Nat.card (quotientProjection hHH').ker : R))
    (hN : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) :
    quotientInvariantsTransition.{w, uR, uG} K hHH' N hK hK' hk ≫
        quotientInvariantsTotalSystemToRepExtend.{w, uR, uG} N K H' hK' hN =
      quotientInvariantsTotalSystemToRepExtend.{w, uR, uG} N K H hK hN := by
  refine hom_ext (NatTrans.ext (funext fun m => ?_))
  obtain ⟨m⟩ := m
  have hX : ∀ m q, N ≤ q → IsZero (((K.quotientInvariantsComplexes H hK).obj m).X q) :=
    fun m q hq => (smoothQuotientInvariants R H).map_isZero (hN m q hq)
  have hX' : ∀ m q, N ≤ q → IsZero (((K.quotientInvariantsComplexes H' hK').obj m).X q) :=
    fun m q hq => (smoothQuotientInvariants R H').map_isZero (hN m q hq)
  have hXRes : ∀ m q, N ≤ q → IsZero ((((K.quotientInvariantsComplexes H hK).map
      ((Rep.resFunctor.{max w uR uG} (k := R) (quotientProjection hHH')).mapHomologicalComplex
        (ComplexShape.up ℕ))).obj m).X q) :=
    fun m q hq => (Rep.resFunctor (quotientProjection hHH')).map_isZero (hX m q hq)
  have h₁ : (groupStandardTotalSystemMap.{w, uG, uR} (quotientProjection hHH')
        (surjective_quotientProjection hHH') hk N
          (K.quotientInvariantsComplexes H hK)).tower.app (op m) ≫
      (groupStandardTotalSystemToExtend.{w, uG, uR} N ((K.quotientInvariantsComplexes H hK).map
        ((Rep.resFunctor.{max w uR uG} (k := R) (quotientProjection hHH')).mapHomologicalComplex
          (ComplexShape.up ℕ))) hXRes).tower.app (op m) =
      ((Rep.resFunctor.{max w uR uG} (k := R) (quotientProjection hHH')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        ((quotientInvariantsTotalSystemToExtend.{w, uR, uG} N K H hK hN).tower.app (op m)) ≫
      (extendMapIso ComplexShape.embeddingUpNat
        (Rep.resFunctor.{max w uR uG} (k := R) (quotientProjection hHH'))
        ((K.quotientInvariantsComplexes H hK).tower.obj (op m))).hom :=
    groupStandardTotalSystemMap_tower_app_comp.{w, uG, uR} (quotientProjection hHH')
      (surjective_quotientProjection hHH') hk N (K.quotientInvariantsComplexes H hK) hX m
  have h₂ := congrArg (fun f => f.tower.app (op m))
    (standardTotalSystemMapOfHom_comp_toExtend N (indResBot.{w, uG, uR} R (G ⧸ H'))
      (indResBotCounit.{w, uG, uR} R (G ⧸ H'))
      (quotientInvariantsComplexesChange.{w, uR, uG} K hHH' hK hK') hXRes hX')
  have h₃ := NatTrans.congr_app (congrArg Hom.tower
    (quotientInvariantsComplexesChange_comp_inclusion.{w, uR, uG} K hHH' hK hK')) (op m)
  have key := extendComparison_comp_eq
    ((quotientInvariantsTotalSystemToExtend.{w, uR, uG} N K H hK hN).tower.app (op m))
    ((groupStandardTotalSystemMap.{w, uG, uR} (quotientProjection hHH')
      (surjective_quotientProjection hHH') hk N (K.quotientInvariantsComplexes H hK)).tower.app
        (op m))
    ((groupStandardTotalSystemToExtend.{w, uG, uR} N ((K.quotientInvariantsComplexes H hK).map
      ((Rep.resFunctor.{max w uR uG} (k := R) (quotientProjection hHH')).mapHomologicalComplex
        (ComplexShape.up ℕ))) hXRes).tower.app (op m))
    ((standardTotalSystemMapOfHom N (indResBot.{w, uG, uR} R (G ⧸ H'))
      (indResBotCounit.{w, uG, uR} R (G ⧸ H'))
      (quotientInvariantsComplexesChange.{w, uR, uG} K hHH' hK hK')).tower.app (op m))
    ((groupStandardTotalSystemToExtend.{w, uG, uR} N (K.quotientInvariantsComplexes H' hK')
      hX').tower.app (op m))
    ((quotientInvariantsComplexesChange.{w, uR, uG} K hHH' hK hK').tower.app (op m))
    ((inflateQuotientInvariantsComplexesHom.{w, uR, uG} K H' hK' ≫
      K.quotientInvariantsComplexesInclusion H' hK').tower.app (op m))
    ((inflateQuotientInvariantsComplexesHom.{w, uR, uG} K H hK ≫
      K.quotientInvariantsComplexesInclusion H hK).tower.app (op m)) h₁ h₂ h₃
  rw [comp_tower, NatTrans.comp_app, quotientInvariantsTransition, comp_tower, NatTrans.comp_app,
    mapCompHom_tower_app, mapHom_tower_app, comp_tower, NatTrans.comp_app,
    extendSystemComparison_tower_app, extendSystemComparison_tower_app]
  exact key

variable [IsTopologicalGroup G] in
/-- Given `ProPInvariantSubcomplexStatement`, for normal pro-`p` subgroups `H' ≤ H` of finite
index with `|H/H'|` and `p` invertible in `R`, the transition morphism is a quasi-isomorphism at
every level `m` at which `H` acts trivially on the cohomology. -/
theorem quasiIso_quotientInvariantsTransition_tower_app
    (hS : ProPInvariantSubcomplexStatement.{uG, uR, max w uR uG}) {p : ℕ}
    (hH : IsProPSubgroup p H) (hH' : IsProPSubgroup p H') (hR : IsUnit (p : R))
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (hK' : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H').map ((K.projection h).f q)))
    (hk : IsUnit (Nat.card (quotientProjection hHH').ker : R))
    (hN : ∀ m q, N ≤ q → IsZero ((K.obj m).X q)) (m : ℕ)
    (htriv : ∀ q (h : H), ((K.toRepComplexes.obj m).homology q).ρ h = LinearMap.id) :
    QuasiIso ((quotientInvariantsTransition.{w, uR, uG} K hHH' N hK hK' hk).tower.app (op m)) := by
  have hE := quasiIso_quotientInvariantsTotalSystemToRepExtend.{w, uR, uG} N K hS hH hR hK hN m
    htriv
  have hE' := quasiIso_quotientInvariantsTotalSystemToRepExtend.{w, uR, uG} N K hS hH' hR hK' hN
    m fun q h => htriv q ⟨h, hHH' h.2⟩
  have h := NatTrans.congr_app (congrArg Hom.tower
    (quotientInvariantsTransition_comp_toRepExtend.{w, uR, uG} K hHH' N hK hK' hk hN)) (op m)
  rw [comp_tower, NatTrans.comp_app] at h
  rw [← h] at hE
  exact (quasiIso_iff_comp_right _ _ (hφ' := hE')).1 hE

end Transition

end DivisibleSystem

end Langlands.Cohomology
