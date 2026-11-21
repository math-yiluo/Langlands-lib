import Langlands.Cohomology.GaloisCartan
import Langlands.Cohomology.GaloisCoveringCech
import Langlands.Cohomology.CoinducedFilteredAcyclic
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # Galois coverings at the level of germs -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.GaloisGerms

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w a b

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (R : Type w) [CommRing R]
variable {I : Type w} [SmallCategory I] [IsCofiltered I]

/-- The germ along a cofiltered system `V : I ⥤ C` of the sections of a module sheaf: the
colimit of `F(V i)` over `Iᵒᵖ`. -/
def germ (V : I ⥤ C) : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{w} R :=
  sheafToPresheaf J (ModuleCat.{w} R) ⋙ (Functor.whiskeringLeft _ _ _).obj V.op ⋙ colim

/-- Restriction of germs along a natural transformation of systems. -/
def germMap {V V' : I ⥤ C} (α : V' ⟶ V) : germ J R V ⟶ germ J R V' :=
  Functor.whiskerLeft (sheafToPresheaf J (ModuleCat.{w} R))
    (Functor.whiskerRight ((Functor.whiskeringLeft _ _ _).map (NatTrans.op α)) colim)

/-- The germ of a section. -/
abbrev germι (V : I ⥤ C) (F : Sheaf J (ModuleCat.{w} R)) (i : I) :
    F.obj.obj (op (V.obj i)) ⟶ (germ J R V).obj F :=
  colimit.ι (V.op ⋙ F.obj) (op i)

omit [IsCofiltered I] in
@[reassoc (attr := simp)]
theorem germι_germMap {V V' : I ⥤ C} (α : V' ⟶ V) (F : Sheaf J (ModuleCat.{w} R)) (i : I) :
    germι J R V F i ≫ (germMap J R α).app F =
      F.obj.map (α.app i).op ≫ germι J R V' F i := by
  simp [germι, germMap, germ]

omit [IsCofiltered I] in
theorem germMap_id (V : I ⥤ C) : germMap J R (𝟙 V) = 𝟙 (germ J R V) := by
  refine NatTrans.ext (funext fun F => ?_)
  apply colimit.hom_ext
  intro i
  have h := germι_germMap J R (𝟙 V) F (unop i)
  rw [NatTrans.id_app, op_id, F.obj.map_id, Category.id_comp] at h
  exact h.trans (Category.comp_id _).symm

omit [IsCofiltered I] in
theorem germMap_comp {V V' V'' : I ⥤ C} (α : V' ⟶ V) (β : V'' ⟶ V') :
    germMap J R (β ≫ α) = germMap J R α ≫ germMap J R β := by
  refine NatTrans.ext (funext fun F => ?_)
  apply colimit.hom_ext
  intro i
  have h := germι_germMap J R (β ≫ α) F (unop i)
  have h1 := germι_germMap_assoc J R α F (unop i) ((germMap J R β).app F)
  have h2 := germι_germMap J R β F (unop i)
  simp only [NatTrans.comp_app, op_comp, Functor.map_comp, Category.assoc] at h
  refine h.trans ?_
  change _ = germι J R V F (unop i) ≫ (germMap J R α).app F ≫ (germMap J R β).app F
  rw [h1, h2]

instance (V : I ⥤ C) : (germ J R V).Additive := by
  dsimp only [germ]
  infer_instance

instance (V : I ⥤ C) : PreservesFiniteLimits (germ J R V) := by
  dsimp only [germ]
  infer_instance

omit [IsCofiltered I] in
theorem map_comp_eq_of_map_eq (F : Sheaf J (ModuleCat.{w} R)) {V₀ : I ⥤ C} {i k k' : Iᵒᵖ}
    (f : i ⟶ k) (r : k ⟶ k') {x y : F.obj.obj (op (V₀.obj i.unop))}
    (h : F.obj.map (V₀.map f.unop).op x = F.obj.map (V₀.map f.unop).op y) :
    F.obj.map (V₀.map (f ≫ r).unop).op x = F.obj.map (V₀.map (f ≫ r).unop).op y := by
  rw [unop_comp, V₀.map_comp, ← GaloisCovering.map_map_apply, ← GaloisCovering.map_map_apply, h]

variable {Γ : Type w} [Group Γ]

/-- A cofiltered system of Galois coverings: natural transformations `p : V' ⟶ V` and
deck transformations of `V'` over `V`, whose components at every index form a
`GaloisCovering`. -/
structure GermGaloisDatum (Γ : Type w) [Group Γ] (V' V : I ⥤ C) where
  p : V' ⟶ V
  deck : Γ → (V' ⟶ V')
  deck_one : deck 1 = 𝟙 V'
  deck_mul : ∀ γ δ : Γ, deck (γ * δ) = deck δ ≫ deck γ
  deck_comp : ∀ γ : Γ, deck γ ≫ p = p
  covering : ∀ i : I, Sieve.ofArrows (fun _ : Unit => V'.obj i) (fun _ => p.app i) ∈ J (V.obj i)
  locally_transitive : ∀ (i : I) {U : C} (f g : U ⟶ V'.obj i), f ≫ p.app i = g ≫ p.app i →
    GaloisCovering.transitivitySieve (fun γ => (deck γ).app i) f g ∈ J U
  locally_free : ∀ (i : I) {U : C} (f : U ⟶ V'.obj i) (γ : Γ),
    f ≫ (deck γ).app i = f → γ = 1 ∨ ⊥ ∈ J U

namespace GermGaloisDatum

variable {J} {V' V : I ⥤ C} (D : GermGaloisDatum J Γ V' V)

omit [IsCofiltered I] in
/-- The Galois covering at one index. -/
@[simps]
def coveringAt (i : I) : GaloisCovering J Γ (V'.obj i) (V.obj i) where
  p := D.p.app i
  covering := D.covering i
  deck γ := (D.deck γ).app i
  deck_one := by rw [D.deck_one]; rfl
  deck_mul γ δ := by rw [D.deck_mul]; rfl
  deck_comp γ := by rw [← NatTrans.comp_app, D.deck_comp]
  locally_transitive := D.locally_transitive i
  locally_free := D.locally_free i

/-- The natural action of `Γ` on germs along `V'`: `γ` acts by restriction along the deck
transformation of `γ⁻¹`. -/
def action : GaloisCartan.NaturalAction Γ (germ J R V') where
  act γ := germMap J R (D.deck γ⁻¹)
  act_one := by rw [inv_one, D.deck_one, germMap_id]
  act_mul γ δ := by rw [mul_inv_rev, D.deck_mul, germMap_comp]

/-- Restriction of germs along `p`. -/
def aug : germ J R V ⟶ germ J R V' := germMap J R D.p

omit [IsCofiltered I] in
theorem aug_act (γ : Γ) : D.aug R ≫ (D.action R).act γ = D.aug R := by
  change germMap J R D.p ≫ germMap J R (D.deck γ⁻¹) = germMap J R D.p
  rw [← germMap_comp, D.deck_comp]

omit [IsCofiltered I] in
theorem germι_aug_apply (F : Sheaf J (ModuleCat.{w} R)) (i : I) (s : F.obj.obj (op (V.obj i))) :
    (D.aug R).app F (germι J R V F i s) = germι J R V' F i (F.obj.map (D.p.app i).op s) := by
  rw [← ConcreteCategory.comp_apply, aug, germι_germMap, ConcreteCategory.comp_apply]

omit [IsCofiltered I] in
theorem germι_act_apply (F : Sheaf J (ModuleCat.{w} R)) (γ : Γ) (i : I)
    (s : F.obj.obj (op (V'.obj i))) :
    ((D.action R).act γ).app F (germι J R V' F i s) =
      germι J R V' F i (F.obj.map ((D.deck γ⁻¹).app i).op s) := by
  rw [← ConcreteCategory.comp_apply]
  change (germι J R V' F i ≫ (germMap J R (D.deck γ⁻¹)).app F) s = _
  rw [germι_germMap, ConcreteCategory.comp_apply]

omit [IsCofiltered I] in
theorem germι_eq_germι_map (F : Sheaf J (ModuleCat.{w} R)) {V₀ : I ⥤ C} {i k : I} (f : k ⟶ i)
    (s : F.obj.obj (op (V₀.obj i))) :
    germι J R V₀ F i s = germι J R V₀ F k (F.obj.map (V₀.map f).op s) := by
  rw [← ConcreteCategory.comp_apply (F.obj.map (V₀.map f).op)]
  exact (congrArg (fun g => g s) (colimit.w (V₀.op ⋙ F.obj) f.op)).symm

/-- Germs of `p` are injective. -/
theorem aug_injective [LocallySmall.{w} C] (F : Sheaf J (ModuleCat.{w} R)) :
    Function.Injective ((D.aug R).app F) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨i, s, rfl⟩ := Concrete.colimit_exists_rep (V.op ⋙ F.obj) x
  change (D.aug R).app F (germι J R V F i.unop s) = 0 at hx
  rw [germι_aug_apply] at hx
  have h0 : germι J R V' F i.unop (F.obj.map (D.p.app i.unop).op s) =
      germι J R V' F i.unop 0 := by rw [hx, map_zero]
  obtain ⟨k, f, g, hfg⟩ := Concrete.colimit_exists_of_rep_eq (V'.op ⋙ F.obj) _ _ h0
  change F.obj.map (V'.map f.unop).op (F.obj.map (D.p.app i.unop).op s) =
    F.obj.map (V'.map g.unop).op 0 at hfg
  rw [map_zero, GaloisCovering.map_map_apply, D.p.naturality f.unop,
    ← GaloisCovering.map_map_apply] at hfg
  have hz : F.obj.map (V.map f.unop).op s = 0 := by
    apply (D.coveringAt k.unop).map_p_injective F
    change F.obj.map (D.p.app k.unop).op _ = F.obj.map (D.p.app k.unop).op 0
    rw [hfg, map_zero]
  change germι J R V F i.unop s = 0
  rw [germι_eq_germι_map R F f.unop s, hz, map_zero]

/-- Galois descent for germs: a germ along `V'` invariant under the finite group `Γ` is the
image of a germ along `V`. -/
theorem exists_aug_eq [LocallySmall.{w} C] [Finite Γ] (F : Sheaf J (ModuleCat.{w} R))
    (y : (germ J R V').obj F) (hy : ∀ γ : Γ, ((D.action R).act γ).app F y = y) :
    ∃ x, (D.aug R).app F x = y := by
  classical
  have := Fintype.ofFinite Γ
  obtain ⟨i, t, rfl⟩ := Concrete.colimit_exists_rep (V'.op ⋙ F.obj) y
  have hγ : ∀ γ : Γ, ∃ (k : Iᵒᵖ) (f : i ⟶ k),
      F.obj.map (V'.map f.unop).op (F.obj.map ((D.deck γ).app i.unop).op t) =
        F.obj.map (V'.map f.unop).op t := by
    intro γ
    have h := hy γ⁻¹
    change ((D.action R).act γ⁻¹).app F (germι J R V' F i.unop t) =
      germι J R V' F i.unop t at h
    rw [germι_act_apply, inv_inv] at h
    obtain ⟨k, f, g, hfg⟩ := Concrete.colimit_exists_of_rep_eq (V'.op ⋙ F.obj) _ _ h
    refine ⟨IsFiltered.coeq f g, f ≫ IsFiltered.coeqHom f g, ?_⟩
    have hfg' : F.obj.map (V'.map f.unop).op (F.obj.map ((D.deck γ).app i.unop).op t) =
        F.obj.map (V'.map g.unop).op t := hfg
    have e1 : F.obj.map (V'.map (IsFiltered.coeqHom f g).unop).op
        (F.obj.map (V'.map g.unop).op t) =
        F.obj.map (V'.map (IsFiltered.coeqHom f g).unop).op
          (F.obj.map (V'.map f.unop).op t) := by
      rw [GaloisCovering.map_map_apply, GaloisCovering.map_map_apply, ← V'.map_comp,
        ← V'.map_comp, ← unop_comp, ← unop_comp, IsFiltered.coeq_condition]
    rw [unop_comp, V'.map_comp, ← GaloisCovering.map_map_apply,
      ← GaloisCovering.map_map_apply, hfg', e1]
  have hcommon : ∀ S : Finset Γ, ∃ (k : Iᵒᵖ) (f : i ⟶ k), ∀ γ ∈ S,
      F.obj.map (V'.map f.unop).op (F.obj.map ((D.deck γ).app i.unop).op t) =
        F.obj.map (V'.map f.unop).op t := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨i, 𝟙 i, fun γ hγ => absurd hγ (Finset.notMem_empty γ)⟩
    | insert γ S _ ih =>
      obtain ⟨k₁, f₁, h₁⟩ := ih
      obtain ⟨k₂, f₂, h₂⟩ := hγ γ
      let a := f₁ ≫ IsFiltered.leftToMax k₁ k₂
      let b := f₂ ≫ IsFiltered.rightToMax k₁ k₂
      refine ⟨IsFiltered.coeq a b, a ≫ IsFiltered.coeqHom a b, ?_⟩
      intro δ hδ
      rcases Finset.mem_insert.1 hδ with rfl | hδ
      · rw [IsFiltered.coeq_condition a b]
        have e : b ≫ IsFiltered.coeqHom a b =
            f₂ ≫ (IsFiltered.rightToMax k₁ k₂ ≫ IsFiltered.coeqHom a b) := by
          simp only [b, Category.assoc]
        rw [e]
        exact map_comp_eq_of_map_eq J R F f₂ _ h₂
      · have e : a ≫ IsFiltered.coeqHom a b =
            f₁ ≫ (IsFiltered.leftToMax k₁ k₂ ≫ IsFiltered.coeqHom a b) := by
          simp only [a, Category.assoc]
        rw [e]
        exact map_comp_eq_of_map_eq J R F f₁ _ (h₁ δ hδ)
  obtain ⟨k, f, hf⟩ := hcommon Finset.univ
  have hinv : ∀ δ : Γ, F.obj.map ((D.coveringAt k.unop).deck δ).op
      (F.obj.map (V'.map f.unop).op t) = F.obj.map (V'.map f.unop).op t := by
    intro δ
    change F.obj.map ((D.deck δ).app k.unop).op (F.obj.map (V'.map f.unop).op t) = _
    rw [GaloisCovering.map_map_apply, ← (D.deck δ).naturality f.unop,
      ← GaloisCovering.map_map_apply]
    exact hf δ (Finset.mem_univ δ)
  obtain ⟨s, hs⟩ := (D.coveringAt k.unop).exists_map_p_eq F _ hinv
  refine ⟨germι J R V F k.unop s, ?_⟩
  rw [germι_aug_apply]
  change germι J R V' F k.unop (F.obj.map ((D.coveringAt k.unop).p).op s) = _
  rw [hs]
  exact (germι_eq_germι_map R F f.unop t).symm

section Acyclic

variable [LocallySmall.{w} C] [HasSheafify J (ModuleCat.{w} R)]

/-- The diagram of representations of `Γ` on sections over the stages of `V'`. -/
def repDiagram (F : Sheaf J (ModuleCat.{w} R)) : Iᵒᵖ ⥤ Rep.{w} R Γ where
  obj i := (D.coveringAt i.unop).rep F
  map {i k} f := Rep.ofHom ⟨(F.obj.map (V'.map f.unop).op).hom, fun γ => LinearMap.ext fun x => by
    change F.obj.map (V'.map f.unop).op (F.obj.map ((D.deck γ⁻¹).app i.unop).op x) =
      F.obj.map ((D.deck γ⁻¹).app k.unop).op (F.obj.map (V'.map f.unop).op x)
    rw [GaloisCovering.map_map_apply, GaloisCovering.map_map_apply,
      (D.deck γ⁻¹).naturality]⟩
  map_id i := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change F.obj.map (V'.map (𝟙 i).unop).op x = x
    rw [unop_id, V'.map_id, op_id, F.obj.map_id]
    rfl
  map_comp {i k l} f g := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change F.obj.map (V'.map (f ≫ g).unop).op x =
      F.obj.map (V'.map g.unop).op (F.obj.map (V'.map f.unop).op x)
    rw [GaloisCovering.map_map_apply, unop_comp, V'.map_comp]

/-- The cocone of germs, with point the representation on germs along `V'`. -/
def repCocone (F : Sheaf J (ModuleCat.{w} R)) : Cocone (D.repDiagram R F) where
  pt := (D.action R).rep F
  ι :=
    { app i := Rep.ofHom ⟨(germι J R V' F i.unop).hom, fun γ => LinearMap.ext fun x =>
        (D.germι_act_apply R F γ i.unop x).symm⟩
      naturality i k f := by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        change germι J R V' F k.unop (F.obj.map (V'.map f.unop).op x) = germι J R V' F i.unop x
        exact (germι_eq_germι_map R F f.unop x).symm }

/-- The germ cocone is a colimit in representations. -/
def repCoconeIsColimit (F : Sheaf J (ModuleCat.{w} R)) : IsColimit (D.repCocone R F) :=
  isColimitOfReflects (forget₂ (Rep.{w} R Γ) (ModuleCat.{w} R))
    (colimit.isColimit (V'.op ⋙ F.obj))

/-- **Injective sheaves are Galois acyclic at the level of germs.** -/
theorem injective_acyclic [Finite Γ] (Inj : Sheaf J (ModuleCat.{w} R)) [Injective Inj] (n : ℕ) :
    IsZero (groupCohomology ((D.action R).rep Inj) (n + 1)) :=
  CoinducedFilteredAcyclic.isZero_groupCohomology_of_isColimit (D.repCoconeIsColimit R Inj)
    (n + 1) (fun i => (D.coveringAt i.unop).isZero_groupCohomology_rep_of_injective R Inj n)

end Acyclic

end GermGaloisDatum

section System

variable [LocallySmall.{w} C] [HasSheafify J (ModuleCat.{w} R)]

/-- A Galois–Čech system of germ functors built from cofiltered Galois data over a common
cofiltered category `I`. The cover data of index `i` are germ Galois data from the system
of the target index to the system of `i`. Only local lifting remains as a hypothesis. -/
def galoisCechSystemOfGerms {ι : Type a} (obj : ι → I ⥤ C) (Cover : ι → Type b)
    (group : ∀ i, Cover i → Type w) [∀ i c, Group (group i c)] [∀ i c, Finite (group i c)]
    (target : ∀ i, Cover i → ι)
    (datum : ∀ i c, GermGaloisDatum J (group i c) (obj (target i c)) (obj i))
    (local_lift : ∀ (S : ShortComplex (Sheaf J (ModuleCat.{w} R))), S.ShortExact →
      ∀ i (s : (germ J R (obj i)).obj S.X₃), ∃ (c : Cover i)
        (t : (germ J R (obj (target i c))).obj S.X₂),
        (germ J R (obj (target i c))).map S.g t = ((datum i c).aug R).app S.X₃ s) :
    GaloisCartan.GaloisCechSystem (fun i => germ J R (obj i)) where
  Cover := Cover
  group := group
  target := target
  action i c := (datum i c).action R
  aug i c := (datum i c).aug R
  aug_injective i c F := (datum i c).aug_injective R F
  aug_act i c γ := (datum i c).aug_act R γ
  exists_aug_eq i c F x hx := (datum i c).exists_aug_eq R F x hx
  local_lift := local_lift
  injective_acyclic i c Inj _ n := (datum i c).injective_acyclic R Inj n

end System

end Langlands.Cohomology.GaloisGerms
