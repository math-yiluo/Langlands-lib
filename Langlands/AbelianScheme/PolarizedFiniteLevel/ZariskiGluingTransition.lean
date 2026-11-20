import Langlands.AbelianScheme.PolarizedFiniteLevel.PullbackCoherence
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Transition maps of polarized isomorphisms onto pulled-back data -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {P : Prerequisites.{u}} {g d n : ℕ}

/-- If every polarized automorphism of `c` is the identity, then any two polarized
isomorphisms out of `c` with the same target are equal. -/
theorem PolarizedIso.eq_of_rigid_source {T : Scheme.{u}} {c c' : Datum P T g d n}
    (hrig : ∀ α : PolarizedIso c c, α = PolarizedIso.refl c) (θ θ' : PolarizedIso c c') :
    θ = θ' := by
  have h := hrig (θ.trans θ'.symm)
  have hhom : θ.abelianIso.hom ≫ θ'.abelianIso.inv = 𝟙 c.abelian :=
    congrArg (fun e : PolarizedIso c c ↦ e.abelianIso.hom) h
  have he : θ.abelianIso = θ'.abelianIso := by
    apply CategoryTheory.Iso.ext
    apply (cancel_mono θ'.abelianIso.inv).mp
    exact hhom.trans θ'.abelianIso.hom_inv_id.symm
  cases θ
  cases θ'
  cases he
  rfl

variable {T T' T'' : Scheme.{u}}

/-- The scheme map `c → c'` over `b : T ⟶ T'` underlying a polarized isomorphism of `c`
with the pullback of `c'` along `b`. -/
def PolarizedIso.overMap {c : Datum P T g d n} {c' : Datum P T' g d n} {b : T ⟶ T'}
    (θ : PolarizedIso c (c'.pullback b)) : c.abelian.X.left ⟶ c'.abelian.X.left :=
  hom θ.abelianIso.hom ≫ pullback.fst c'.abelian.X.hom b

theorem PolarizedIso.hom_snd {c : Datum P T g d n} {c' : Datum P T' g d n} {b : T ⟶ T'}
    (θ : PolarizedIso c (c'.pullback b)) :
    hom θ.abelianIso.hom ≫ pullback.snd c'.abelian.X.hom b = c.abelian.X.hom :=
  Over.w (groupHom θ.abelianIso.hom).hom.hom

theorem PolarizedIso.overMap_w {c : Datum P T g d n} {c' : Datum P T' g d n} {b : T ⟶ T'}
    (θ : PolarizedIso c (c'.pullback b)) :
    θ.overMap ≫ c'.abelian.X.hom = c.abelian.X.hom ≫ b := by
  rw [PolarizedIso.overMap, Category.assoc, pullback.condition, ← Category.assoc,
    θ.hom_snd]

/-- The square formed by the transition map over `b` is cartesian. -/
theorem PolarizedIso.isPullback_overMap {c : Datum P T g d n} {c' : Datum P T' g d n}
    {b : T ⟶ T'} (θ : PolarizedIso c (c'.pullback b)) :
    IsPullback θ.overMap c.abelian.X.hom c'.abelian.X.hom b :=
  IsPullback.of_iso_pullback ⟨θ.overMap_w⟩ (underlyingSchemeIso θ.abelianIso) rfl θ.hom_snd

/-- Over an identity base map, the transition map of the unique polarized isomorphism
is the identity. -/
theorem PolarizedIso.overMap_eq_id {c : Datum P T g d n}
    (hrig : ∀ α : PolarizedIso c c, α = PolarizedIso.refl c) {b : T ⟶ T} (hb : b = 𝟙 T)
    (θ : PolarizedIso c (c.pullback b)) : θ.overMap = 𝟙 _ := by
  subst hb
  have hθ : θ = (c.pullbackIdIso).symm := PolarizedIso.eq_of_rigid_source hrig _ _
  subst hθ
  have h1 : hom (baseChangeIdIso c.abelian).hom = pullback.fst c.abelian.X.hom (𝟙 T) :=
    GroupScheme.baseChangeIdIso_hom_left c.abelian.toGrp
  change hom (baseChangeIdIso c.abelian).inv ≫ pullback.fst c.abelian.X.hom (𝟙 T) = 𝟙 _
  rw [← h1, ← hom_comp, Iso.inv_hom_id, hom_id]

/-- Transition maps compose along composite base maps. -/
theorem PolarizedIso.overMap_comp {c : Datum P T g d n} {c' : Datum P T' g d n}
    {c'' : Datum P T'' g d n} (hrig : ∀ α : PolarizedIso c c, α = PolarizedIso.refl c)
    {b₁ : T ⟶ T'} {b₂ : T' ⟶ T''} {b₃ : T ⟶ T''} (hb : b₁ ≫ b₂ = b₃)
    (θ₁ : PolarizedIso c (c'.pullback b₁)) (θ₂ : PolarizedIso c' (c''.pullback b₂))
    (θ₃ : PolarizedIso c (c''.pullback b₃)) :
    θ₁.overMap ≫ θ₂.overMap = θ₃.overMap := by
  subst hb
  have hθ : θ₃ = θ₁.trans ((θ₂.pullback b₁).trans (c''.pullbackCompIso b₂ b₁).symm) :=
    PolarizedIso.eq_of_rigid_source hrig _ _
  subst hθ
  have h1 : hom (baseChangeCompIso b₂ b₁ c''.abelian).inv ≫
      pullback.fst c''.abelian.X.hom (b₁ ≫ b₂) =
      pullback.fst (pullback.snd c''.abelian.X.hom b₂) b₁ ≫
        pullback.fst c''.abelian.X.hom b₂ :=
    GroupScheme.baseChangeCompIso_inv_fst b₂ b₁ c''.abelian.toGrp
  have h2 : hom ((baseChange b₁).map θ₂.abelianIso.hom) ≫
      pullback.fst (pullback.snd c''.abelian.X.hom b₂) b₁ =
      pullback.fst c'.abelian.X.hom b₁ ≫ hom θ₂.abelianIso.hom := by
    change ((Over.pullback b₁).map (groupHom θ₂.abelianIso.hom).hom.hom).left ≫ _ = _
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  change hom θ₁.abelianIso.hom ≫ pullback.fst c'.abelian.X.hom b₁ ≫
      hom θ₂.abelianIso.hom ≫ pullback.fst c''.abelian.X.hom b₂ =
    (hom θ₁.abelianIso.hom ≫ hom ((baseChange b₁).map θ₂.abelianIso.hom) ≫
      hom (baseChangeCompIso b₂ b₁ c''.abelian).inv) ≫
        pullback.fst c''.abelian.X.hom (b₁ ≫ b₂)
  simp only [Category.assoc]
  erw [h1]
  erw [reassoc_of% h2]

end Langlands.AbelianScheme.PolarizedFiniteLevel
