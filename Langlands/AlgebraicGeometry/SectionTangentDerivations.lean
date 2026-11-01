import Langlands.AlgebraicGeometry.PointTangentSpace
import Langlands.AlgebraicGeometry.RelativeDifferentialsUniversal
import Langlands.CommutativeAlgebra.PointDerivationCotangent

/-!
# Tangent sections over a one-point base and point derivations of the stalk

For a scheme `X` over a one-point scheme `S` with a section `e`, the global sections of the
published tangent module `tangentAtSection X e` are identified with the point derivations of the
stalk of `X` at `e(pt)` with values in the stalk of `S` at `pt`. The identification is the
composite of the local-to-global morphism equivalence over `⊤`, the pullback-pushforward
adjunction along `e`, the universal property of the relative differential sheaf, and a skyscraper
comparison between relative derivations into `e_* O_S` and point derivations of the stalk.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace Langlands.Scheme.Modules

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- Local morphisms over the top open are global morphisms of module sheaves. -/
def localHomTopEquiv (M N : S.Modules) : LocalHom M N ⊤ ≃ (M ⟶ N) where
  toFun f :=
    { val :=
      { app := fun V => f.val.app (op (Over.mk (homOfLE le_top : V.unop ⟶ ⊤)))
        naturality := fun {V W} i =>
          f.val.naturality (Over.homMk (U := Over.mk (homOfLE le_top : W.unop ⟶ ⊤))
            (V := Over.mk (homOfLE le_top : V.unop ⟶ ⊤)) i.unop).op } }
  invFun φ :=
    { val :=
      { app := fun V => φ.val.app (op V.unop.left)
        naturality := fun {V W} i => φ.val.naturality i.unop.left.op } }
  left_inv f := by ext V i x; rfl
  right_inv φ := by rfl

lemma localHomTopEquiv_app (M N : S.Modules) (f : LocalHom M N ⊤) (V : S.Opens) :
    (localHomTopEquiv M N f).app V = (forget₂ _ Ab).map (LocalHom.app f (homOfLE le_top)) := rfl

end Langlands.Scheme.Modules

namespace Langlands.Scheme.SectionPoint

section OnePoint

variable {S : AlgebraicGeometry.Scheme.{u}} [Subsingleton S] (pt : S)

lemma eq_top_of_mem {V : S.Opens} (h : pt ∈ V) : V = ⊤ :=
  eq_top_iff.2 fun y _ => Subsingleton.elim pt y ▸ h

lemma eq_bot_of_notMem {V : S.Opens} (h : pt ∉ V) : V = ⊥ :=
  eq_bot_iff.2 fun y hy => (h (Subsingleton.elim y pt ▸ hy)).elim

lemma subsingleton_of_notMem {V : S.Opens} (h : pt ∉ V) : Subsingleton Γ(S, V) := by
  obtain rfl := eq_bot_of_notMem pt h
  infer_instance

lemma germ_injective {V : S.Opens} (h : pt ∈ V) :
    Function.Injective (S.presheaf.germ V pt h) := by
  intro a b hab
  obtain ⟨W, hW, iU, iV, e⟩ := S.presheaf.germ_eq pt h h a b hab
  obtain rfl : W = V := (eq_top_of_mem pt hW).trans (eq_top_of_mem pt h).symm
  rw [Subsingleton.elim iU (𝟙 W), Subsingleton.elim iV (𝟙 W)] at e
  simpa using e

lemma germ_surjective {V : S.Opens} (h : pt ∈ V) :
    Function.Surjective (S.presheaf.germ V pt h) := by
  intro t
  obtain ⟨W, hW, a, rfl⟩ := S.presheaf.exists_germ_eq t
  obtain rfl : W = V := (eq_top_of_mem pt hW).trans (eq_top_of_mem pt h).symm
  exact ⟨a, rfl⟩

lemma germ_bijective {V : S.Opens} (h : pt ∈ V) :
    Function.Bijective (S.presheaf.germ V pt h) :=
  ⟨germ_injective pt h, germ_surjective pt h⟩

/-- The inverse of the germ map on an open containing the point. -/
def germInv {V : S.Opens} (h : pt ∈ V) : S.presheaf.stalk pt → Γ(S, V) :=
  (Equiv.ofBijective _ (germ_bijective pt h)).symm

@[simp]
lemma germ_germInv {V : S.Opens} (h : pt ∈ V) (t : S.presheaf.stalk pt) :
    S.presheaf.germ V pt h (germInv pt h t) = t :=
  (Equiv.ofBijective _ (germ_bijective pt h)).apply_symm_apply t

lemma section_ext {V : S.Opens} {a b : Γ(S, V)}
    (h : ∀ hV : pt ∈ V, S.presheaf.germ V pt hV a = S.presheaf.germ V pt hV b) : a = b := by
  by_cases hV : pt ∈ V
  · exact germ_injective pt hV (h hV)
  · have := subsingleton_of_notMem pt hV
    exact Subsingleton.elim a b

end OnePoint

section Skyscraper

variable {Y S : AlgebraicGeometry.Scheme.{u}} {f : Y ⟶ S} {s : S ⟶ Y} (pt : S)

variable (s) in
/-- The pushforward of the structure module of `S` along `s`. -/
abbrev pointModule : Y.Modules :=
  (AlgebraicGeometry.Scheme.Modules.pushforward s).obj (Langlands.SchemeModule.structureModule S)

variable (s) in
/-- Sections of `pointModule s` over `U` are the sections of `S` over `s ⁻¹ᵁ U`. -/
def sectionEquiv (U : Y.Opens) : Γ(pointModule s, U) ≃+ Γ(S, s ⁻¹ᵁ U) where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

lemma sectionEquiv_smul (U : Y.Opens) (a : Γ(Y, U)) (m : Γ(pointModule s, U)) :
    sectionEquiv s U (a • m) = s.app U a * sectionEquiv s U m := rfl

lemma sectionEquiv_restrict {U V : Y.Opens} (i : V ⟶ U) (m : Γ(pointModule s, U)) :
    sectionEquiv s V ((pointModule s).presheaf.map i.op m) =
      S.presheaf.map (homOfLE (s.preimage_mono (leOfHom i))).op (sectionEquiv s U m) := rfl

/-- The germ at `pt` of the value of a relative derivation into `pointModule s`. -/
def stalkValue (D : RelativeDerivation f (pointModule s)) (U : Y.Opens) (hx : s pt ∈ U)
    (a : Γ(Y, U)) : S.presheaf.stalk pt :=
  S.presheaf.germ (s ⁻¹ᵁ U) pt (s.mem_preimage.2 hx) (sectionEquiv s U (D.app U a))

lemma germ_sectionEquiv_smul (U : Y.Opens) (hx : s pt ∈ U) (a : Γ(Y, U))
    (m : Γ(pointModule s, U)) :
    S.presheaf.germ (s ⁻¹ᵁ U) pt (s.mem_preimage.2 hx) (sectionEquiv s U (a • m)) =
      s.stalkMap pt (Y.presheaf.germ U (s pt) hx a) *
        S.presheaf.germ (s ⁻¹ᵁ U) pt (s.mem_preimage.2 hx) (sectionEquiv s U m) := by
  rw [sectionEquiv_smul, map_mul, Scheme.Hom.germ_stalkMap_apply]

lemma germ_sectionEquiv_restrict {U V : Y.Opens} (i : V ⟶ U) (hx : s pt ∈ V)
    (m : Γ(pointModule s, U)) :
    S.presheaf.germ (s ⁻¹ᵁ V) pt (s.mem_preimage.2 hx)
        (sectionEquiv s V ((pointModule s).presheaf.map i.op m)) =
      S.presheaf.germ (s ⁻¹ᵁ U) pt (s.mem_preimage.2 (leOfHom i hx)) (sectionEquiv s U m) := by
  rw [sectionEquiv_restrict]
  exact S.presheaf.germ_res_apply _ pt _ _

lemma stalkValue_restrict (D : RelativeDerivation f (pointModule s)) {U V : Y.Opens}
    (i : V ⟶ U) (hx : s pt ∈ V) (a : Γ(Y, U)) :
    stalkValue pt D V hx (Y.presheaf.map i.op a) = stalkValue pt D U (leOfHom i hx) a := by
  rw [stalkValue, RelativeDerivation.app_restrict, germ_sectionEquiv_restrict pt i hx]
  rfl

lemma stalkValue_eq_of_germ_eq (D : RelativeDerivation f (pointModule s)) {U V : Y.Opens}
    (hxU : s pt ∈ U) (hxV : s pt ∈ V) (a : Γ(Y, U)) (b : Γ(Y, V))
    (h : Y.presheaf.germ U (s pt) hxU a = Y.presheaf.germ V (s pt) hxV b) :
    stalkValue pt D U hxU a = stalkValue pt D V hxV b := by
  obtain ⟨W, hW, iU, iV, e⟩ := Y.presheaf.germ_eq (s pt) hxU hxV a b h
  rw [← stalkValue_restrict pt D iU hW, ← stalkValue_restrict pt D iV hW, e]

/-- The function on the stalk at `s pt` induced by a relative derivation into `pointModule s`. -/
def stalkFun (D : RelativeDerivation f (pointModule s)) (t : Y.presheaf.stalk (s pt)) :
    S.presheaf.stalk pt :=
  stalkValue pt D (Y.presheaf.exists_germ_eq t).choose
    (Y.presheaf.exists_germ_eq t).choose_spec.choose
    (Y.presheaf.exists_germ_eq t).choose_spec.choose_spec.choose

lemma stalkFun_germ (D : RelativeDerivation f (pointModule s)) (U : Y.Opens) (hx : s pt ∈ U)
    (a : Γ(Y, U)) : stalkFun pt D (Y.presheaf.germ U (s pt) hx a) = stalkValue pt D U hx a :=
  stalkValue_eq_of_germ_eq pt D _ _ _ _
    (Y.presheaf.exists_germ_eq (Y.presheaf.germ U (s pt) hx a)).choose_spec.choose_spec.choose_spec

lemma exists_common_germ {y : Y} (t₁ t₂ : Y.presheaf.stalk y) :
    ∃ (U : Y.Opens) (hy : y ∈ U) (a b : Γ(Y, U)),
      Y.presheaf.germ U y hy a = t₁ ∧ Y.presheaf.germ U y hy b = t₂ := by
  obtain ⟨U₁, h₁, a, rfl⟩ := Y.presheaf.exists_germ_eq t₁
  obtain ⟨U₂, h₂, b, rfl⟩ := Y.presheaf.exists_germ_eq t₂
  exact ⟨U₁ ⊓ U₂, ⟨h₁, h₂⟩, Y.presheaf.map (homOfLE inf_le_left).op a,
    Y.presheaf.map (homOfLE inf_le_right).op b, Y.presheaf.germ_res_apply _ _ _ _,
    Y.presheaf.germ_res_apply _ _ _ _⟩

variable (f s) in
/-- The map from the global sections of the base to the stalk at `s pt`. -/
def baseMap : Γ(S, ⊤) →+* Y.presheaf.stalk (s pt) :=
  (f.app ⊤ ≫ Y.presheaf.germ (f ⁻¹ᵁ ⊤) (s pt) (f.mem_preimage.2 (Opens.mem_top _))).hom

/-- The point derivation of the stalk induced by a relative derivation into `pointModule s`. -/
def stalkDerivation (D : RelativeDerivation f (pointModule s)) :
    Langlands.CommutativeAlgebra.PointDerivation.derivations (baseMap f s pt)
      (s.stalkMap pt).hom :=
  ⟨AddMonoidHom.mk' (stalkFun pt D) fun t₁ t₂ => by
      obtain ⟨U, hx, a, b, rfl, rfl⟩ := exists_common_germ t₁ t₂
      rw [← map_add, stalkFun_germ, stalkFun_germ, stalkFun_germ, stalkValue, stalkValue,
        stalkValue, RelativeDerivation.app_add, map_add, map_add],
    fun t₁ t₂ => by
      obtain ⟨U, hx, a, b, rfl, rfl⟩ := exists_common_germ t₁ t₂
      simp only [AddMonoidHom.mk'_apply]
      rw [← map_mul, stalkFun_germ, stalkFun_germ, stalkFun_germ, stalkValue, stalkValue,
        stalkValue, RelativeDerivation.app_mul, map_add, map_add, germ_sectionEquiv_smul,
        germ_sectionEquiv_smul],
    fun c => by
      simp only [AddMonoidHom.mk'_apply]
      change stalkFun pt D (Y.presheaf.germ (f ⁻¹ᵁ ⊤) (s pt)
        (f.mem_preimage.2 (Opens.mem_top _)) (f.app ⊤ c)) = 0
      rw [stalkFun_germ, stalkValue, RelativeDerivation.app_base, map_zero, map_zero]⟩

lemma stalkDerivation_germ (D : RelativeDerivation f (pointModule s)) (U : Y.Opens)
    (hx : s pt ∈ U) (a : Γ(Y, U)) :
    ((stalkDerivation pt D : _) : Y.presheaf.stalk (s pt) →+ S.presheaf.stalk pt)
      (Y.presheaf.germ U (s pt) hx a) =
        S.presheaf.germ (s ⁻¹ᵁ U) pt (s.mem_preimage.2 hx) (sectionEquiv s U (D.app U a)) :=
  stalkFun_germ pt D U hx a

variable [Subsingleton S]

open Langlands.CommutativeAlgebra.PointDerivation in
lemma pointModule_ext {U : Y.Opens} {m m' : Γ(pointModule s, U)}
    (h : ∀ hx : s pt ∈ U,
      S.presheaf.germ (s ⁻¹ᵁ U) pt (s.mem_preimage.2 hx) (sectionEquiv s U m) =
        S.presheaf.germ (s ⁻¹ᵁ U) pt (s.mem_preimage.2 hx) (sectionEquiv s U m')) :
    m = m' :=
  (sectionEquiv s U).injective (section_ext pt fun hV => h (s.mem_preimage.1 hV))

open Langlands.CommutativeAlgebra.PointDerivation

open Classical in
/-- The sections of the relative derivation induced by a point derivation of the stalk. -/
def ofStalkFun (δ : derivations (baseMap f s pt) (s.stalkMap pt).hom) (U : Y.Opens)
    (a : Γ(Y, U)) : Γ(pointModule s, U) :=
  if hx : s pt ∈ U then
    (sectionEquiv s U).symm (germInv pt (s.mem_preimage.2 hx)
      ((δ : Y.presheaf.stalk (s pt) →+ S.presheaf.stalk pt) (Y.presheaf.germ U (s pt) hx a)))
  else 0

lemma germ_ofStalkFun (δ : derivations (baseMap f s pt) (s.stalkMap pt).hom) (U : Y.Opens)
    (hx : s pt ∈ U) (a : Γ(Y, U)) :
    S.presheaf.germ (s ⁻¹ᵁ U) pt (s.mem_preimage.2 hx) (sectionEquiv s U (ofStalkFun pt δ U a)) =
      (δ : Y.presheaf.stalk (s pt) →+ S.presheaf.stalk pt) (Y.presheaf.germ U (s pt) hx a) := by
  simp only [ofStalkFun, hx, ↓reduceDIte, AddEquiv.apply_symm_apply, germ_germInv]

/-- The additive map on sections induced by a point derivation of the stalk. -/
def ofStalkApp (δ : derivations (baseMap f s pt) (s.stalkMap pt).hom) (U : Y.Opens) :
    Γ(Y, U) →+ Γ(pointModule s, U) :=
  AddMonoidHom.mk' (ofStalkFun pt δ U) fun a b => pointModule_ext pt fun hx => by
    have e1 := germ_ofStalkFun pt δ U hx (a + b)
    have e2 := germ_ofStalkFun pt δ U hx a
    have e3 := germ_ofStalkFun pt δ U hx b
    rw [map_add, map_add] at e1
    rw [e1, map_add, map_add, e2, e3]

/-- The relative derivation into `pointModule s` induced by a point derivation of the stalk. -/
def ofStalkDerivation (δ : derivations (baseMap f s pt) (s.stalkMap pt).hom) :
    RelativeDerivation f (pointModule s) where
  d {U} := ofStalkApp pt δ U.unop
  d_mul {U} a b := by
    induction U using Opposite.rec with | op U => ?_
    change Γ(Y, U) at a b
    refine pointModule_ext pt fun hx => ?_
    have e1 := germ_ofStalkFun pt δ U hx (a * b)
    have e2 := germ_ofStalkFun pt δ U hx a
    have e3 := germ_ofStalkFun pt δ U hx b
    have e4 := germ_sectionEquiv_smul pt U hx a (ofStalkFun pt δ U b)
    have e5 := germ_sectionEquiv_smul pt U hx b (ofStalkFun pt δ U a)
    have e6 := derivations_mul δ (Y.presheaf.germ U (s pt) hx a)
      (Y.presheaf.germ U (s pt) hx b)
    have e7 : S.presheaf.germ (s ⁻¹ᵁ U) pt (s.mem_preimage.2 hx)
        (sectionEquiv s U (a • ofStalkFun pt δ U b + b • ofStalkFun pt δ U a)) =
      S.presheaf.germ (s ⁻¹ᵁ U) pt (s.mem_preimage.2 hx)
          (sectionEquiv s U (a • ofStalkFun pt δ U b)) +
        S.presheaf.germ (s ⁻¹ᵁ U) pt (s.mem_preimage.2 hx)
          (sectionEquiv s U (b • ofStalkFun pt δ U a)) := by
      rw [map_add, map_add]
    rw [e4, e5, e2, e3] at e7
    rw [map_mul] at e1
    exact e1.trans (e6.trans e7.symm)
  d_map {U V} i a := pointModule_ext pt fun hx => by
    have h1 := germ_ofStalkFun pt δ V.unop hx (Y.presheaf.map i a)
    have h2 := germ_sectionEquiv_restrict pt i.unop hx (ofStalkFun pt δ U.unop a)
    have h3 := germ_ofStalkFun pt δ U.unop (leOfHom i.unop hx) a
    have h4 := Y.presheaf.germ_res_apply i.unop (s pt) hx a
    exact h1.trans ((congrArg _ h4).trans (h3.symm.trans h2.symm))
  d_app {V} b := pointModule_ext pt fun hx => by
    induction V using Opposite.rec with | op V => ?_
    obtain rfl : V = ⊤ := eq_top_of_mem (f (s pt)) hx
    have e1 := germ_ofStalkFun pt δ (f ⁻¹ᵁ ⊤) hx (f.app ⊤ b)
    exact e1.trans ((derivations_base δ b).trans
      ((congrArg (S.presheaf.germ (s ⁻¹ᵁ (f ⁻¹ᵁ ⊤)) pt (s.mem_preimage.2 hx))
        (map_zero (sectionEquiv s (f ⁻¹ᵁ ⊤)))).trans (map_zero _)).symm)

lemma germ_ofStalkDerivation (δ : derivations (baseMap f s pt) (s.stalkMap pt).hom)
    (U : Y.Opens) (hx : s pt ∈ U) (a : Γ(Y, U)) :
    S.presheaf.germ (s ⁻¹ᵁ U) pt (s.mem_preimage.2 hx)
        (sectionEquiv s U ((ofStalkDerivation pt δ).app U a)) =
      (δ : Y.presheaf.stalk (s pt) →+ S.presheaf.stalk pt) (Y.presheaf.germ U (s pt) hx a) :=
  germ_ofStalkFun pt δ U hx a

/-- Relative derivations into the pushforward of the structure sheaf of a one-point scheme along
a point are the point derivations of the stalk. -/
def stalkDerivationEquiv :
    RelativeDerivation f (pointModule s) ≃ derivations (baseMap f s pt) (s.stalkMap pt).hom where
  toFun := stalkDerivation pt
  invFun := ofStalkDerivation pt
  left_inv D := by
    ext U a
    exact pointModule_ext pt fun hx => (germ_ofStalkDerivation pt _ U.unop hx a).trans
      (stalkDerivation_germ pt D U.unop hx a)
  right_inv δ := by
    apply Subtype.ext
    ext t
    obtain ⟨U, hx, a, rfl⟩ := Y.presheaf.exists_germ_eq t
    exact (stalkDerivation_germ pt _ U hx a).trans (germ_ofStalkDerivation pt δ U hx a)

end Skyscraper

section Tangent

variable {S : AlgebraicGeometry.Scheme.{u}} (X : Over S) (e : Over.mk (𝟙 S) ⟶ X) (pt : S)

/-- The morphism `Ω_{X/S} ⟶ e_* O_S` adjoint to the morphism `e^* Ω_{X/S} ⟶ O_S` given by a
section of the tangent module. -/
def tangentAdjoint (t : Γ(tangentAtSection X e, ⊤)) :
    relativeDifferentials X.hom ⟶ pointModule e.left :=
  (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction e.left).homEquiv _ _
    (Modules.localHomTopEquiv _ _ t)

/-- The value of the relative derivation attached to a tangent section. -/
def tangentEval (t : Γ(tangentAtSection X e, ⊤)) (U : X.left.Opens) (a : Γ(X.left, U)) :
    Γ(pointModule e.left, U) :=
  (tangentAdjoint X e t).app U ((relativeDifferentialsDerivation X.hom).app U a)

lemma tangentEval_add (t t' : Γ(tangentAtSection X e, ⊤)) (U : X.left.Opens) (a : Γ(X.left, U)) :
    tangentEval X e (t + t') U a = tangentEval X e t U a + tangentEval X e t' U a := by
  simp only [tangentEval, tangentAdjoint, Adjunction.homEquiv_unit]
  rfl

lemma tangentEval_smul (c : Γ(S, ⊤)) (t : Γ(tangentAtSection X e, ⊤)) (U : X.left.Opens)
    (a : Γ(X.left, U)) :
    sectionEquiv e.left U (tangentEval X e (c • t) U a) =
      (Over.mk (𝟙 S)).left.presheaf.map (homOfLE le_top : e.left ⁻¹ᵁ U ⟶ ⊤).op c *
        sectionEquiv e.left U (tangentEval X e t U a) := by
  simp only [tangentEval, tangentAdjoint, Adjunction.homEquiv_unit]
  rfl

variable [Subsingleton S]

/-- The source of a section is the one-point base. -/
theorem subsingletonSectionSource : Subsingleton (Over.mk (𝟙 S)).left := ‹Subsingleton S›

attribute [local instance] subsingletonSectionSource

open Langlands.CommutativeAlgebra.PointDerivation in
/-- Over a one-point base, the tangent module at a section is the space of point derivations of
the stalk at the image point. -/
def tangentDerivationEquiv :
    Γ(tangentAtSection X e, ⊤) ≃ derivations (baseMap X.hom e.left pt) (e.left.stalkMap pt).hom :=
  ((Modules.localHomTopEquiv _ _).trans
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction e.left).homEquiv _ _).trans
      (relativeDifferentialsHomEquiv X.hom _))).trans (stalkDerivationEquiv pt)

lemma tangentDerivationEquiv_germ (t : Γ(tangentAtSection X e, ⊤)) (U : X.left.Opens)
    (hx : e.left pt ∈ U) (a : Γ(X.left, U)) :
    ((tangentDerivationEquiv X e pt t : _) :
        X.left.presheaf.stalk (e.left pt) →+ (Over.mk (𝟙 S)).left.presheaf.stalk pt)
      (X.left.presheaf.germ U (e.left pt) hx a) =
      (Over.mk (𝟙 S)).left.presheaf.germ (e.left ⁻¹ᵁ U) pt (e.left.mem_preimage.2 hx)
        (sectionEquiv e.left U (tangentEval X e t U a)) := by
  exact stalkDerivation_germ pt _ U hx a

lemma tangentDerivationEquiv_add (t t' : Γ(tangentAtSection X e, ⊤)) :
    tangentDerivationEquiv X e pt (t + t') =
      tangentDerivationEquiv X e pt t + tangentDerivationEquiv X e pt t' := by
  apply Subtype.ext
  ext r
  obtain ⟨U, hx, a, rfl⟩ := X.left.presheaf.exists_germ_eq r
  rw [Submodule.coe_add, AddMonoidHom.add_apply, tangentDerivationEquiv_germ,
    tangentDerivationEquiv_germ, tangentDerivationEquiv_germ, tangentEval_add, map_add, map_add]

lemma tangentDerivationEquiv_smul (c : Γ(S, ⊤)) (t : Γ(tangentAtSection X e, ⊤)) :
    tangentDerivationEquiv X e pt (c • t) =
      (Over.mk (𝟙 S)).left.presheaf.germ ⊤ pt trivial c • tangentDerivationEquiv X e pt t := by
  apply Subtype.ext
  ext r
  obtain ⟨U, hx, a, rfl⟩ := X.left.presheaf.exists_germ_eq r
  rw [Submodule.coe_smul, AddMonoidHom.smul_apply, tangentDerivationEquiv_germ,
    tangentDerivationEquiv_germ, tangentEval_smul, map_mul, smul_eq_mul,
    TopCat.Presheaf.germ_res_apply]

end Tangent

/-- The base map composed with the stalk map of a section is the germ map of the base. -/
lemma stalkMap_baseMap {S : AlgebraicGeometry.Scheme.{u}} (X : Over S) (e : Over.mk (𝟙 S) ⟶ X)
    (pt : S) (c : Γ(S, ⊤)) :
    e.left.stalkMap pt (baseMap X.hom e.left pt c) =
      (Over.mk (𝟙 S)).left.presheaf.germ ⊤ pt trivial c := by
  have key : ∀ (g : (Over.mk (𝟙 S)).left ⟶ S), g = 𝟙 S → ∀ h : pt ∈ g ⁻¹ᵁ ⊤,
      (Over.mk (𝟙 S)).left.presheaf.germ (g ⁻¹ᵁ ⊤) pt h (g.app ⊤ c) =
        (Over.mk (𝟙 S)).left.presheaf.germ ⊤ pt trivial c := by
    rintro g rfl h
    rfl
  exact (Scheme.Hom.germ_stalkMap_apply e.left _ pt _ _).trans (key _ (Over.w e) _)

end Langlands.Scheme.SectionPoint
