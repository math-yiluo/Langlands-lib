/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleHypercover
public import WeilConjectures.CategoryTheory.ProperFaceMatchingObject
public import WeilConjectures.AlgebraicGeometry.SemiRepresentableObject
import WeilConjectures.AlgebraicGeometry.SRMatchingObjectOneMember
import Mathlib.Tactic

/-!
# Canonical matching schemes for simplicial étale schemes

Source: Stacks, Tags 0186 and 021D. The finite diagram includes every lower simplex,
so its limit directly supplies the universal property used by `IsEtaleHypercover`.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v w


open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.EtaleSimplicialMatching

/-- A simplex of dimension strictly less than `n` in the standard `n`-simplex. -/
abbrev Index (n : ℕ) := Σ m : Fin n, (⦋m.val⦌ ⟶ ⦋n⦌)

instance (n : ℕ) : SmallCategory (Index n) where
  Hom a b := {f : ⦋a.1.val⦌ ⟶ ⦋b.1.val⦌ // f ≫ b.2 = a.2}
  id a := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.val ≫ g.val, by rw [Category.assoc, g.property, f.property]⟩
  id_comp f := Subtype.ext (Category.id_comp _)
  comp_id f := Subtype.ext (Category.comp_id _)
  assoc f g h := Subtype.ext (Category.assoc _ _ _)

noncomputable instance (n : ℕ) : Fintype (Index n) := Fintype.ofFinite _

noncomputable instance (n : ℕ) : FinCategory (Index n) where
  fintypeHom a b := Fintype.ofFinite {f : ⦋a.1.val⦌ ⟶ ⦋b.1.val⦌ // f ≫ b.2 = a.2}

/-- Forget a lower simplex to its domain. -/
def domain (n : ℕ) : Index n ⥤ SimplexCategory where
  obj a := ⦋a.1.val⦌
  map f := f.val

/-- The finite matching diagram. -/
def diagram {X : Scheme.{u}} (U : SimplicialObject X.Etale) (n : ℕ) :
    (Index n)ᵒᵖ ⥤ X.Etale := (domain n).op ⋙ U


/-- The injective image face of a lower simplex. -/
noncomputable def imageFace {n : ℕ} (Δ : SimplexCategory) (h : Δ.len < n)
    (θ : Δ ⟶ ⦋n⦌) : SimplicialObject.ProperFaceCategory n :=
  ⟨Over.mk (image.ι θ),
    lt_of_le_of_lt (SimplexCategory.len_le_of_epi (factorThruImage θ)) h,
    (by
      change Function.Injective (image.ι θ).toOrderHom
      exact SimplexCategory.mono_iff_injective.mp inferInstance)⟩

/-- Extend a proper-face family by the canonical image factorization of each simplex. -/
noncomputable def extendProperFamily {C : Type u} [Category.{v} C]
    (U : SimplicialObject C) (n : ℕ) {T : C}
    (p : (Functor.const _).obj T ⟶ U.properFaceDiagram n) :
    (Functor.const _).obj T ⟶ (domain n).op ⋙ U where
  app a := p.app (op (imageFace _ a.unop.1.isLt a.unop.2)) ≫
    U.map (factorThruImage a.unop.2).op
  naturality {a b} f := by
    let sq : Arrow.mk b.unop.2 ⟶ Arrow.mk a.unop.2 :=
      Arrow.homMk f.unop.val (𝟙 _) (by simpa using f.unop.property)
    let β := image.map sq
    have hβ : β ≫ image.ι a.unop.2 = image.ι b.unop.2 := by
      simpa [β, sq] using image.map_ι sq
    have he : factorThruImage b.unop.2 ≫ β = f.unop.val ≫
        factorThruImage a.unop.2 := image.factor_map sq
    let g : imageFace _ b.unop.1.isLt b.unop.2 ⟶
        imageFace _ a.unop.1.isLt a.unop.2 :=
      ObjectProperty.homMk (Over.homMk β hβ)
    have hg := p.naturality g.op
    change 𝟙 T ≫ p.app (op (imageFace _ b.unop.1.isLt b.unop.2)) =
      p.app (op (imageFace _ a.unop.1.isLt a.unop.2)) ≫ U.map β.op at hg
    change 𝟙 T ≫ (p.app (op (imageFace _ b.unop.1.isLt b.unop.2)) ≫
      U.map (factorThruImage b.unop.2).op) =
      (p.app (op (imageFace _ a.unop.1.isLt a.unop.2)) ≫
        U.map (factorThruImage a.unop.2).op) ≫ U.map f.unop.val.op
    rw [Category.id_comp] at hg ⊢
    rw [hg, Category.assoc, Category.assoc, ← U.map_comp, ← U.map_comp,
      ← op_comp, ← op_comp, he]

lemma extendProperFamily_restrict {C : Type u} [Category.{v} C]
    (U : SimplicialObject C) (n : ℕ) {T : C}
    (p : (Functor.const _).obj T ⟶ U.properFaceDiagram n)
    (a : SimplicialObject.ProperFaceCategory n) :
    (extendProperFamily U n p).app (op ⟨⟨a.obj.left.len, a.property.1⟩, a.obj.hom⟩) =
      p.app (op a) := by
  let g : a ⟶ imageFace _ a.property.1 a.obj.hom :=
    ObjectProperty.homMk (Over.homMk (factorThruImage a.obj.hom) (image.fac _))
  change p.app (op (imageFace _ a.property.1 a.obj.hom)) ≫
    U.map (factorThruImage a.obj.hom).op = p.app (op a)
  have hg := p.naturality g.op
  change 𝟙 T ≫ p.app (op a) = p.app (op (imageFace _ a.property.1 a.obj.hom)) ≫
    U.map (factorThruImage a.obj.hom).op at hg
  simpa only [Category.id_comp] using hg.symm

/-- The matching scheme is a genuine finite limit in the small étale category. -/
noncomputable def matching {X : Scheme.{u}} (U : SimplicialObject X.Etale) (n : ℕ) :
    X.Etale := limit (diagram U n)

/-- Its projections are indexed by all lower simplices. -/
noncomputable def projection {X : Scheme.{u}} (U : SimplicialObject X.Etale) (n : ℕ)
    (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ ⦋n⦌) :
    matching U n ⟶ U.obj (op Δ) :=
  limit.π (diagram U n) (op ⟨⟨Δ.len, h⟩, θ⟩)

lemma projection_naturality {X : Scheme.{u}} (U : SimplicialObject X.Etale) (n : ℕ)
    (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
    (α : Δ' ⟶ Δ) (θ : Δ ⟶ ⦋n⦌) :
    projection U n Δ h θ ≫ U.map α.op = projection U n Δ' h' (α ≫ θ) := by
  exact limit.w (diagram U n) (show (⟨⟨Δ'.len, h'⟩, α ≫ θ⟩ : Index n) ⟶
    ⟨⟨Δ.len, h⟩, θ⟩ from ⟨α, rfl⟩).op

/-- The cone of all simplicial operators from degree `n`. -/
def matchingCone {X : Scheme.{u}} (U : SimplicialObject X.Etale) (n : ℕ) :
    Cone (diagram U n) where
  pt := U.obj (op ⦋n⦌)
  π :=
    { app a := U.map a.unop.2.op
      naturality {a b} f := by
        change 𝟙 _ ≫ U.map b.unop.2.op =
          U.map a.unop.2.op ≫ U.map f.unop.val.op
        rw [Category.id_comp, ← U.map_comp, ← op_comp, f.unop.property] }

/-- The canonical matching arrow. -/
noncomputable def matchingMap {X : Scheme.{u}} (U : SimplicialObject X.Etale) (n : ℕ) :
    U.obj (op ⦋n⦌) ⟶ matching U n := limit.lift _ (matchingCone U n)

lemma matchingMap_projection {X : Scheme.{u}} (U : SimplicialObject X.Etale) (n : ℕ)
    (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ ⦋n⦌) :
    matchingMap U n ≫ projection U n Δ h θ = U.map θ.op :=
  limit.lift_π (matchingCone U n) (op ⟨⟨Δ.len, h⟩, θ⟩)


/-- Naturality of the canonical finite matching limit. -/
noncomputable def matchingNat {X : Scheme.{u}} {U V : SimplicialObject X.Etale}
    (c : U ⟶ V) (n : ℕ) : matching U n ⟶ matching V n :=
  limit.lift (diagram V n)
    { pt := matching U n
      π :=
        { app a := projection U n _ a.unop.1.isLt a.unop.2 ≫ c.app (op ⦋a.unop.1.val⦌)
          naturality {a b} f := by
            change 𝟙 _ ≫ (projection U n _ _ b.unop.2 ≫ c.app _) =
              (projection U n _ _ a.unop.2 ≫ c.app _) ≫ V.map f.unop.val.op
            rw [Category.id_comp, Category.assoc, ← c.naturality,
              ← Category.assoc, projection_naturality, f.unop.property] } }

lemma matchingNat_projection {X : Scheme.{u}} {U V : SimplicialObject X.Etale}
    (c : U ⟶ V) (n : ℕ) (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ ⦋n⦌) :
    matchingNat c n ≫ projection V n Δ h θ = projection U n Δ h θ ≫ c.app (op Δ) :=
  limit.lift_π (F := diagram V n) _ (op (show Index n from ⟨⟨Δ.len, h⟩, θ⟩))

/-- The canonical matching object also carries the usual proper-face cone. -/
noncomputable def properCone {X : Scheme.{u}} (U : SimplicialObject X.Etale) (n : ℕ) :
    Cone (U.properFaceDiagram n) where
  pt := matching U n
  π :=
    { app a := projection U n a.unop.obj.left a.unop.property.1 a.unop.obj.hom
      naturality {a b} f := by
        change 𝟙 _ ≫ projection U n _ _ b.unop.obj.hom =
          projection U n _ _ a.unop.obj.hom ≫ U.map f.unop.hom.left.op
        rw [Category.id_comp, projection_naturality, Over.w] }

/-- The lower-simplex matching limit and the proper-face matching limit coincide.
Source: Stacks, Tag 0186. Factor every lower simplex through its image; this extends
proper-face families uniquely and naturally to all lower simplices.
(auxiliary; not a blueprint node) -/
noncomputable def properConeIsLimit {X : Scheme.{u}} (U : SimplicialObject X.Etale)
    (n : ℕ) : IsLimit (properCone U n) where
  lift s := limit.lift (diagram U n) ⟨s.pt, extendProperFamily U n s.π⟩
  fac s a := by
    change limit.lift (diagram U n) ⟨s.pt, extendProperFamily U n s.π⟩ ≫
      projection U n _ _ a.unop.obj.hom = _
    rw [show projection U n _ _ a.unop.obj.hom =
      limit.π (diagram U n)
        (op ⟨⟨a.unop.obj.left.len, a.unop.property.1⟩, a.unop.obj.hom⟩) from rfl]
    rw [limit.lift_π]
    exact extendProperFamily_restrict U n s.π a.unop
  uniq s f hf := by
    apply limit.hom_ext (F := diagram U n)
    intro a
    let im := imageFace _ a.unop.1.isLt a.unop.2
    have hfac : projection U n _ a.unop.1.isLt a.unop.2 =
        projection U n _ im.property.1 im.obj.hom ≫
          U.map (factorThruImage a.unop.2).op := by
      rw [projection_naturality]
      exact congrArg (projection U n _ a.unop.1.isLt) (image.fac a.unop.2).symm
    change f ≫ projection U n _ _ a.unop.2 = _
    rw [hfac, ← Category.assoc]
    have hfi := hf (op im)
    change f ≫ projection U n _ im.property.1 im.obj.hom = s.π.app (op im) at hfi
    rw [hfi, limit.lift_π]
    rfl

/-- The matching limit remains a limit among all schemes over the base.
Source: Stacks, Tags 0186 and 021D: the étale inclusion preserves finite limits.
(auxiliary; not a blueprint node) -/
theorem matching_universal {X : Scheme.{u}} (U : SimplicialObject X.Etale) (n : ℕ)
    (T : Over X)
    (p : ∀ (Δ : SimplexCategory), Δ.len < n → (Δ ⟶ ⦋n⦌) →
      (T ⟶ (Scheme.Etale.forget X).obj (U.obj (op Δ))))
    (hp : ∀ (Δ Δ' : SimplexCategory) (h : Δ.len < n) (h' : Δ'.len < n)
      (α : Δ' ⟶ Δ) (θ : Δ ⟶ ⦋n⦌),
      p Δ h θ ≫ (Scheme.Etale.forget X).map (U.map α.op) = p Δ' h' (α ≫ θ)) :
    ∃! f : T ⟶ (Scheme.Etale.forget X).obj (matching U n),
      ∀ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ ⦋n⦌),
        f ≫ (Scheme.Etale.forget X).map (projection U n Δ h θ) = p Δ h θ := by
  let c : Cone (diagram U n ⋙ Scheme.Etale.forget X) :=
    { pt := T
      π :=
        { app a := p ⦋a.unop.1.val⦌ a.unop.1.isLt a.unop.2
          naturality {a b} f := by
            change 𝟙 T ≫ p _ _ b.unop.2 =
              p _ _ a.unop.2 ≫ (Scheme.Etale.forget X).map (U.map f.unop.val.op)
            rw [Category.id_comp, hp, f.unop.property] } }
  let hlim := isLimitOfPreserves (Scheme.Etale.forget X) (limit.isLimit (diagram U n))
  refine ⟨hlim.lift c, ?_, ?_⟩
  · intro Δ h θ
    exact hlim.fac c (op ⟨⟨Δ.len, h⟩, θ⟩)
  · intro f hf
    apply hlim.uniq c f
    intro a
    exact hf ⦋a.unop.1.val⦌ a.unop.1.isLt a.unop.2

/-- Surjectivity of the canonical matching arrows gives precisely the required hypercover
witnesses; their data are finite limits, not witnesses chosen from a mere existence theorem.
Source: Stacks, Definition 01G5 and Tag 0186.
(auxiliary; not a blueprint node) -/
theorem isEtaleHypercover_of_matchingCover {X : Scheme.{u}}
    (U : SimplicialObject X.Etale) (hU : ∀ n, Surjective (matchingMap U n).left) :
    IsEtaleHypercover U := by
  intro n
  exact ⟨matching U n, projection U n, matchingMap U n,
    projection_naturality U n, matching_universal U n,
    matchingMap_projection U n, hU n⟩

/-- Any matching witnesses in the hypercover predicate give covers of the canonical
matching schemes as well. Source: Stacks, Tag 0186, uniqueness of matching limits.
(auxiliary; not a blueprint node) -/
theorem matchingCover_of_isEtaleHypercover {X : Scheme.{u}}
    (U : SimplicialObject X.Etale) (hU : IsEtaleHypercover U) (n : ℕ) :
    Surjective (matchingMap U n).left := by
  classical
  obtain ⟨M, π, μ, hπ, hM, hμ, hcover⟩ := hU n
  let F := Scheme.Etale.forget X
  let c : Cone (diagram U n) :=
    { pt := M
      π :=
        { app a := π _ a.unop.1.isLt a.unop.2
          naturality {a b} f := by
            change 𝟙 M ≫ π _ _ b.unop.2 = π _ _ a.unop.2 ≫ U.map f.unop.val.op
            rw [Category.id_comp, hπ, f.unop.property] } }
  let r : M ⟶ matching U n := limit.lift _ c
  have hr (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ ⦋n⦌) :
      r ≫ projection U n Δ h θ = π Δ h θ :=
    limit.lift_π c (op ⟨⟨Δ.len, h⟩, θ⟩)
  obtain ⟨q₀, hq₀, _⟩ := hM (F.obj (matching U n))
    (fun Δ h θ ↦ F.map (projection U n Δ h θ)) (by
      intro Δ Δ' h h' α θ
      change F.map (projection U n Δ h θ) ≫ F.map (U.map α.op) = _
      rw [← F.map_comp, projection_naturality])
  let q : matching U n ⟶ M := F.preimage q₀
  have hq (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ ⦋n⦌) :
      q ≫ π Δ h θ = projection U n Δ h θ := by
    apply F.map_injective
    simpa only [F.map_comp, q, F.map_preimage] using hq₀ Δ h θ
  have hqr : q ≫ r = 𝟙 (matching U n) := by
    apply limit.hom_ext
    intro a
    change (q ≫ r) ≫ projection U n _ _ a.unop.2 =
      𝟙 _ ≫ projection U n _ _ a.unop.2
    rw [Category.assoc, hr, hq, Category.id_comp]
  have hmur : μ ≫ r = matchingMap U n := by
    apply limit.hom_ext
    intro a
    change (μ ≫ r) ≫ projection U n _ _ a.unop.2 =
      matchingMap U n ≫ projection U n _ _ a.unop.2
    rw [Category.assoc, hr, hμ, matchingMap_projection]
  let := hcover
  constructor
  intro x
  obtain ⟨y, hy⟩ := μ.left.surjective (q.left x)
  refine ⟨y, ?_⟩
  have hleft : q.left ≫ r.left = 𝟙 _ := congrArg (fun f ↦ f.left) hqr
  have hmuleft : μ.left ≫ r.left = (matchingMap U n).left :=
    congrArg (fun f ↦ f.left) hmur
  rw [← hmuleft]
  change r.left (μ.left y) = x
  rw [hy]
  exact congrArg (fun f ↦ f x) hleft

/-- The full scheme matching predicate supplies the singleton semi-representable
hypercover predicate required by finite-simplex lifting.
Source: Stacks, Tags 01G5 and 0186, and the one-member matching comparison.
(auxiliary; not a blueprint node) -/
theorem isSemiRepresentableHypercover_of_isEtaleHypercover {X : Scheme.{u}}
    (U : SimplicialObject X.Etale) (hU : IsEtaleHypercover U) :
    Scheme.IsSemiRepresentableHypercover (U ⋙ FormalCoproduct.incl.{w} X.Etale) := by
  classical
  obtain ⟨M, π, μ, _, hlim, hμ, _, _, heq⟩ :=
    Scheme.sr_matching_object_one_member.{w} X U
  apply heq.mpr
  intro n
  let c : Cone (U.properFaceDiagram n) := Cone.mk (M n) (π n)
  let hc : IsLimit c := isLimitOfReflects (Scheme.Etale.forget X) (hlim n).some
  let e : M n ≅ matching U n := hc.conePointUniqueUpToIso (properConeIsLimit U n)
  have hm : μ n ≫ e.hom = matchingMap U n := by
    apply (properConeIsLimit U n).hom_ext
    intro a
    change (μ n ≫ e.hom) ≫ projection U n _ _ a.unop.obj.hom =
      matchingMap U n ≫ projection U n _ _ a.unop.obj.hom
    rw [Category.assoc,
      show e.hom ≫ projection U n _ _ a.unop.obj.hom = (π n).app a from
        hc.conePointUniqueUpToIso_hom_comp (properConeIsLimit U n) a,
      hμ, matchingMap_projection]
  let _ : Surjective (matchingMap U n).left := matchingCover_of_isEtaleHypercover U hU n
  let _ : IsIso e.inv.left := inferInstanceAs
    (IsIso ((Scheme.Etale.forget X ⋙ Over.forget X).map e.inv))
  have hm' : μ n = matchingMap U n ≫ e.inv := by
    rw [← hm, Category.assoc, e.hom_inv_id, Category.comp_id]
  refine ⟨inferInstance, ?_⟩
  rw [hm']
  change Surjective ((matchingMap U n).left ≫ e.inv.left)
  infer_instance

end AlgebraicGeometry.EtaleSimplicialMatching
