import Langlands.Shimura.SplitLevelTower
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Level spaces at split levels

For a splitting `e : G ≃ₜ* H × H'` and a level `K₀` of `H`, the level space
`Γ \ (X × G) / e⁻¹ (K₀ × K')` is the level space `Γ \ ((X × H ⧸ K₀) × H') / K'` of `H'`, where
`e ∘ ι = (ι₁, ι₂)` and `Γ` acts on `H ⧸ K₀` through `ι₁`. See `SplitLevelSpace.md`.
-/

noncomputable section

universe u v v₁ v₂ z w t

namespace Langlands.Shimura

open CategoryTheory CategoryTheory.Limits Opposite CompactOpenLevel

namespace LevelSpace

section Domain

variable {Γ : Type u} {H : Type v₁} {X : Type z} [Group Γ] [Group H] [MulAction Γ X]

variable (X) in
/-- The domain `X × H ⧸ K₀` of the level spaces away from a factor `H`. It carries the diagonal
action of `Γ`: on `X` by the given action and on `H ⧸ K₀` by left multiplication through
`ι₁ : Γ →* H`. -/
def AwayDomain (_ι₁ : Γ →* H) (K₀ : Subgroup H) : Type (max z v₁) :=
  X × (H ⧸ K₀)

variable (ι₁ : Γ →* H) (K₀ : Subgroup H)

instance : MulAction Γ (AwayDomain X ι₁ K₀) :=
  letI : MulAction Γ (H ⧸ K₀) := MulAction.compHom _ ι₁
  inferInstanceAs (MulAction Γ (X × (H ⧸ K₀)))

/-- A point of the away domain from a point of `X` and a coset of `K₀`. -/
def AwayDomain.mk (x : X) (c : H ⧸ K₀) : AwayDomain X ι₁ K₀ :=
  (x, c)

theorem AwayDomain.smul_mk (γ : Γ) (x : X) (h : H) :
    γ • AwayDomain.mk ι₁ K₀ x (h : H ⧸ K₀) = AwayDomain.mk ι₁ K₀ (γ • x) ((ι₁ γ * h : H) : H ⧸ K₀) :=
  rfl

instance [TopologicalSpace X] [TopologicalSpace H] : TopologicalSpace (AwayDomain X ι₁ K₀) :=
  inferInstanceAs (TopologicalSpace (X × (H ⧸ K₀)))

end Domain

section Restriction

variable {Γ : Type u} {G : Type v} {H : Type v₁} {H' : Type v₂} [Group Γ] [Group G] [Group H]
  [Group H'] [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace H']

/-- The first component `Γ → H` of `e ∘ ι`. -/
def factorRestriction (ι : Γ →* G) (e : G ≃ₜ* H × H') : Γ →* H :=
  (MonoidHom.fst H H').comp ((e : G →* H × H').comp ι)

/-- The second component `Γ → H'` of `e ∘ ι`. -/
def awayRestriction (ι : Γ →* G) (e : G ≃ₜ* H × H') : Γ →* H' :=
  (MonoidHom.snd H H').comp ((e : G →* H × H').comp ι)

/-- The two components of `e ∘ ι`. -/
theorem apply_eq_factorRestriction_awayRestriction (ι : Γ →* G) (e : G ≃ₜ* H × H') (γ : Γ) :
    e (ι γ) = (factorRestriction ι e γ, awayRestriction ι e γ) :=
  rfl

end Restriction

section Split

variable {Γ : Type u} {G : Type v} {H : Type v₁} {H' : Type v₂} {X : Type z} [Group Γ] [Group G]
  [Group H] [Group H'] [MulAction Γ X] [TopologicalSpace G] [TopologicalSpace H]
  [TopologicalSpace H'] (ι : Γ →* G) (e : G ≃ₜ* H × H') (ι₁ : Γ →* H) {ι₂ : Γ →* H'}
  (hι : ∀ γ, e (ι γ) = (ι₁ γ, ι₂ γ)) (K₀ : CompactOpenLevel H) (K' : CompactOpenLevel H')

/-- The point of `(X × H ⧸ K₀) × H'` attached to a point `(x, g)` of `X × G`. -/
def awayPoint (x : X × G) : AwayDomain X ι₁ K₀.subgroup × H' :=
  (AwayDomain.mk ι₁ K₀.subgroup x.1 ((e x.2).1 : H ⧸ K₀.subgroup), (e x.2).2)

/-- The point `(x, e⁻¹ (h, h'))` of the level space at `e⁻¹ (K₀ × K')` attached to
`((x, h K₀), h')`; it does not depend on the representative `h`. -/
def awayInvFun (p : AwayDomain X ι₁ K₀.subgroup × H') :
    LevelSpace (X := X) ι (transport e.symm (prod K₀ K')).subgroup :=
  Quotient.liftOn' p.1.2 (fun h => mk _ (p.1.1, e.symm (h, p.2))) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab
    rw [mk_eq_mk]
    refine ⟨1, e.symm (a⁻¹ * b, 1), ?_, (one_smul Γ _).symm, ?_⟩
    · rw [mem_transport_symm_prod, e.apply_symm_apply]
      exact ⟨hab, K'.subgroup.one_mem⟩
    · rw [map_one, one_mul, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel_left, mul_one]

theorem awayInvFun_mk (x : X) (h : H) (h' : H') :
    awayInvFun ι e ι₁ K₀ K' (AwayDomain.mk ι₁ K₀.subgroup x (h : H ⧸ K₀.subgroup), h') =
      mk _ (x, e.symm (h, h')) :=
  rfl

variable {ι e ι₁}

include hι in
theorem awayPoint_respects (x y : X × G)
    (hxy : levelSetoid ι (transport e.symm (prod K₀ K')).subgroup x y) :
    levelSetoid ι₂ K'.subgroup (awayPoint e ι₁ K₀ x) (awayPoint e ι₁ K₀ y) := by
  obtain ⟨γ, k, hk, hy₁, hy₂⟩ := hxy
  rw [mem_transport_symm_prod] at hk
  have he₁ : (e y.2).1 = ι₁ γ * (e x.2).1 * (e k).1 := by
    rw [hy₂, map_mul, map_mul, hι]
    rfl
  have he₂ : (e y.2).2 = ι₂ γ * (e x.2).2 * (e k).2 := by
    rw [hy₂, map_mul, map_mul, hι]
    rfl
  refine ⟨γ, (e k).2, hk.2, ?_, he₂⟩
  change AwayDomain.mk ι₁ K₀.subgroup y.1 ((e y.2).1 : H ⧸ K₀.subgroup) =
    AwayDomain.mk ι₁ K₀.subgroup (γ • x.1) ((ι₁ γ * (e x.2).1 : H) : H ⧸ K₀.subgroup)
  rw [hy₁, he₁, QuotientGroup.mk_mul_of_mem _ hk.1]

include hι in
theorem awayInvFun_respects (p q : AwayDomain X ι₁ K₀.subgroup × H')
    (hpq : levelSetoid ι₂ K'.subgroup p q) :
    awayInvFun ι e ι₁ K₀ K' p = awayInvFun ι e ι₁ K₀ K' q := by
  obtain ⟨⟨x, c⟩, h'⟩ := p
  obtain ⟨⟨y, d⟩, j'⟩ := q
  induction c using QuotientGroup.induction_on with
  | H a =>
  obtain ⟨γ, k', hk', h₁, h₂⟩ := hpq
  change AwayDomain.mk ι₁ K₀.subgroup y d =
    AwayDomain.mk ι₁ K₀.subgroup (γ • x) ((ι₁ γ * a : H) : H ⧸ K₀.subgroup) at h₁
  change j' = ι₂ γ * h' * k' at h₂
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₁
  subst h₂
  change mk _ (x, e.symm (a, h')) = mk _ (γ • x, e.symm (ι₁ γ * a, ι₂ γ * h' * k'))
  rw [mk_eq_mk]
  refine ⟨γ, e.symm (1, k'), ?_, rfl, ?_⟩
  · rw [mem_transport_symm_prod, e.apply_symm_apply]
    exact ⟨K₀.subgroup.one_mem, hk'⟩
  · apply e.injective
    simp only [map_mul, e.apply_symm_apply, hι, Prod.mk_mul_mk, mul_one]

variable (X) in
/-- The level space of `G` at `e⁻¹ (K₀ × K')` is the level space of `H'` at `K'` for the domain
`X × H ⧸ K₀`. -/
def awayEquiv :
    LevelSpace (X := X) ι (transport e.symm (prod K₀ K')).subgroup ≃
      LevelSpace (X := AwayDomain X ι₁ K₀.subgroup) ι₂ K'.subgroup where
  toFun := Quotient.map (awayPoint e ι₁ K₀) (awayPoint_respects hι K₀ K')
  invFun := Quotient.lift (awayInvFun ι e ι₁ K₀ K') (awayInvFun_respects hι K₀ K')
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h x =>
      change mk _ (x.1, e.symm ((e x.2).1, (e x.2).2)) = mk _ x
      rw [Prod.mk.eta, e.symm_apply_apply]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h p =>
      obtain ⟨⟨x, c⟩, h'⟩ := p
      induction c using QuotientGroup.induction_on with
      | H a =>
        change mk _ (awayPoint e ι₁ K₀ (x, e.symm (a, h'))) = mk _ _
        simp only [awayPoint, e.apply_symm_apply]
        rfl

@[simp] theorem awayEquiv_mk (x : X × G) :
    awayEquiv X hι K₀ K' (mk _ x) = mk _ (awayPoint e ι₁ K₀ x) :=
  rfl

@[simp] theorem awayEquiv_symm_mk (x : X) (h : H) (h' : H') :
    (awayEquiv X hι K₀ K').symm
        (mk _ (AwayDomain.mk ι₁ K₀.subgroup x (h : H ⧸ K₀.subgroup), h')) =
      mk _ (x, e.symm (h, h')) :=
  rfl

/-- Right translation by `e⁻¹ (1, h')` corresponds to right translation by `h'`. -/
theorem awayEquiv_translate {K' L' : CompactOpenLevel H'} (h' : H')
    (hg : ∀ k ∈ (transport e.symm (prod K₀ K')).subgroup,
      (e.symm (1, h'))⁻¹ * k * e.symm (1, h') ∈ (transport e.symm (prod K₀ L')).subgroup)
    (hh : ∀ k ∈ K'.subgroup, h'⁻¹ * k * h' ∈ L'.subgroup)
    (q : LevelSpace (X := X) ι (transport e.symm (prod K₀ K')).subgroup) :
    awayEquiv X hι K₀ L' (translate (e.symm (1, h')) hg q) =
      translate h' hh (awayEquiv X hι K₀ K' q) := by
  induction q using Quotient.inductionOn with
  | h x =>
    change mk _ (awayPoint e ι₁ K₀ (x.1, x.2 * e.symm (1, h'))) =
      mk _ ((awayPoint e ι₁ K₀ x).1, (awayPoint e ι₁ K₀ x).2 * h')
    simp only [awayPoint, map_mul, e.apply_symm_apply, Prod.fst_mul, Prod.snd_mul, mul_one]

variable [TopologicalSpace X] [IsTopologicalGroup H]

omit [MulAction Γ X] [IsTopologicalGroup H] in
variable (e ι₁) in
theorem continuous_awayPoint : Continuous (awayPoint (X := X) e ι₁ K₀) := by
  have he : Continuous fun x : X × G => e x.2 := e.continuous.comp continuous_snd
  exact (continuous_fst.prodMk (QuotientGroup.continuous_mk.comp
    (continuous_fst.comp he))).prodMk (continuous_snd.comp he)

omit [MulAction Γ X] [Group H'] in
variable (ι₁) in
/-- The projection `((x, h), h') ↦ ((x, h K₀), h')`, an open quotient map. -/
theorem isOpenQuotientMap_awayProjection :
    IsOpenQuotientMap (fun p : (X × H) × H' =>
      ((AwayDomain.mk ι₁ K₀.subgroup p.1.1 (p.1.2 : H ⧸ K₀.subgroup), p.2) :
        AwayDomain X ι₁ K₀.subgroup × H')) :=
  (IsOpenQuotientMap.id.prodMap QuotientGroup.isOpenQuotientMap_mk).prodMap IsOpenQuotientMap.id

variable (ι e ι₁) in
theorem continuous_awayInvFun : Continuous (awayInvFun (X := X) ι e ι₁ K₀ K') := by
  rw [← (isOpenQuotientMap_awayProjection ι₁ K₀).continuous_comp_iff]
  change Continuous fun p : (X × H) × H' => mk (ι := ι) _ (p.1.1, e.symm (p.1.2, p.2))
  exact (continuous_mk _).comp (continuous_fst.comp continuous_fst |>.prodMk
    (e.symm.continuous.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))

variable (X) in
/-- The level space of `G` at `e⁻¹ (K₀ × K')` is homeomorphic to the level space of `H'` at
`K'` for the domain `X × H ⧸ K₀`. -/
def awayHomeomorph :
    LevelSpace (X := X) ι (transport e.symm (prod K₀ K')).subgroup ≃ₜ
      LevelSpace (X := AwayDomain X ι₁ K₀.subgroup) ι₂ K'.subgroup where
  toEquiv := awayEquiv X hι K₀ K'
  continuous_toFun :=
    (continuous_awayPoint e ι₁ K₀).quotient_map' (awayPoint_respects hι K₀ K')
  continuous_invFun :=
    isQuotientMap_quot_mk.continuous_iff.mpr (continuous_awayInvFun ι e ι₁ K₀ K')

@[simp] theorem awayHomeomorph_apply
    (q : LevelSpace (X := X) ι (transport e.symm (prod K₀ K')).subgroup) :
    awayHomeomorph X hι K₀ K' q = awayEquiv X hι K₀ K' q :=
  rfl

end Split

section Tower

variable {Γ : Type u} {G H H' : Type v} (X : Type z) [Group Γ] [Group G] [Group H] [Group H']
  [MulAction Γ X] [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace X] [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup H']
  {ι : Γ →* G} {e : G ≃ₜ* H × H'} {ι₁ : Γ →* H} {ι₂ : Γ →* H'}
  (hι : ∀ γ, e (ι γ) = (ι₁ γ, ι₂ γ)) (K₀ : CompactOpenLevel H)

/-- The tower of level spaces of `G` at the levels `e⁻¹ (K₀ × K')` is the tower of level spaces of
`H'` for the domain `X × H ⧸ K₀`. -/
def awayTowerIso :
    (awayOver e K₀).functor ⋙ tower (X := X) (ι := ι) ≅
      tower (X := AwayDomain X ι₁ K₀.subgroup) (ι := ι₂) :=
  NatIso.ofComponents (fun K' => TopCat.isoOfHomeo (awayHomeomorph X hι K₀ K'))
    fun {K' L'} a => by
      ext q
      exact awayEquiv_translate hι K₀ a.element ((awayOver e K₀).functor.map a).respects
        a.respects q

@[simp] theorem awayTowerIso_hom_app_apply (K' : CompactOpenLevel H')
    (q : LevelSpace (X := X) ι (transport e.symm (prod K₀ K')).subgroup) :
    (awayTowerIso X hι K₀).hom.app K' q = awayEquiv X hι K₀ K' q :=
  rfl

variable {C : Type w} [Category C] (P : TopCat.{max v z}ᵒᵖ ⥤ C)

/-- For any presheaf `P` on spaces, the away tower at `K₀` of `K ↦ P (Γ \ (X × G) / K)` is the
presheaf `K' ↦ P (Γ \ ((X × H ⧸ K₀) × H') / K')` on the levels of `H'`. -/
def awayTowerPresheafIso :
    LevelColimit.awayTower e K₀ ((tower (X := X) (ι := ι)).op ⋙ P) ≅
      (tower (X := AwayDomain X ι₁ K₀.subgroup) (ι := ι₂)).op ⋙ P :=
  Functor.isoWhiskerRight (NatIso.op (awayTowerIso X hι K₀)).symm P

theorem awayTowerPresheafIso_hom_app (K' : CompactOpenLevel H') :
    (awayTowerPresheafIso X hι K₀ P).hom.app (op K') =
      P.map ((awayTowerIso X hι K₀).inv.app K').op :=
  rfl

/-- The colimit over `K'` of the away tower, with its action of `H'`, is the colimit of the level
spaces of `H'` for the domain `X × H ⧸ K₀`. -/
def awayActionIso [HasColimitsOfShape (Ordered H')ᵒᵖ C] :
    LevelColimit.action (LevelColimit.awayTower e K₀ ((tower (X := X) (ι := ι)).op ⋙ P)) ≅
      LevelColimit.action ((tower (X := AwayDomain X ι₁ K₀.subgroup) (ι := ι₂)).op ⋙ P) :=
  (LevelColimit.functor H' C).mapIso (awayTowerPresheafIso X hι K₀ P)

/-- For a presheaf of modules `P`, the smooth representation of `H'` on the colimit of the away
tower is the smooth representation on the colimit of the level spaces of `H'` for the domain
`X × H ⧸ K₀`. -/
def awaySmoothRepIso {R : Type t} [CommRing R] [HasColimitsOfShape (Ordered G)ᵒᵖ (ModuleCat.{w} R)]
    [HasColimitsOfShape (Ordered H')ᵒᵖ (ModuleCat.{w} R)]
    (P : TopCat.{max v z}ᵒᵖ ⥤ ModuleCat.{w} R) :
    LevelColimit.awaySmoothRep e K₀ ((tower (X := X) (ι := ι)).op ⋙ P)
        (isLevelTrivial_tower ι P) ≅
      LevelColimit.smoothRep ((tower (X := AwayDomain X ι₁ K₀.subgroup) (ι := ι₂)).op ⋙ P)
        (isLevelTrivial_tower ι₂ P) :=
  ObjectProperty.isoMk _ ((Rep.ActionToRep R H').mapIso (awayActionIso X hι K₀ P))

end Tower

end LevelSpace

end Langlands.Shimura
