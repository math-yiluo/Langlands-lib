/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTransport
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapDelta

/-!
# Pullback of torsors and of their classes in `H¹`

Let `g : X ⟶ Y` be a morphism of schemes, `G` an abelian sheaf on the small étale site of `Y`,
`G'` one on the small étale site of `X` and `φ : G ⟶ g_* G'` a morphism, with transpose
`φ^♭ : g^* G ⟶ G'`. Let `P` be a `G`-torsor and `P'` a `G'`-torsor, and suppose given maps
`σ : P(V) → P'(V ×_Y X)`, natural in the étale `Y`-scheme `V` and equivariant along `φ`. Then the
class of `P'` in `H¹(X, G')` is the image of the class of `P` under the pullback map

`H¹(Y, G) ⟶ H¹(X, g^* G) ⟶ H¹(X, G')`

(`AlgebraicGeometry.Etale.classH1_eq_map_cohomologyMap_of_equivariant`). In other words `P'` is
the torsor obtained from `P` by pullback along `g` and extension of the structure group along
`φ^♭`.

Writing `P` and `P'` as torsors of local lifts of global sections `s` and `s'` for injective
resolutions `0 → G → I → Q → 0` and `0 → G' → I' → Q' → 0`, the pullback map sends the class
`δ(s)` to `δ'(ψ(g^* s))` for a morphism of short exact sequences
`(φ^♭, χ, ψ) : g^* (0 → G → I → Q → 0) ⟶ (0 → G' → I' → Q' → 0)`. The local differences
`b'(σ x) - χ(g^* (b x))` of the lifts of `σ x` and of `x` are invariant, hence glue to a global
section `c` of `I'` with `d' c = s' - ψ(g^* s)`.

We also record that the classes of torsors, the connecting homomorphisms and the degree-zero
identification `H⁰(G) ≅ G(T)` do not depend on the choice of the terminal object `T` of the site.

## Main statements

- `CategoryTheory.Sheaf.Torsor.classH1_congr`: the class of a torsor does not depend on the
  terminal object.
- `AlgebraicGeometry.Etale.equiv₀_cohomologyMap`: in degree zero the pullback map is the
  pullback of global sections along the unit of `g^* ⊣ g_*`.
- `AlgebraicGeometry.Etale.classH1_eq_map_cohomologyMap_of_equivariant`: compatibility of the
  pullback map on `H¹` with the pullback of torsors.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Limits Opposite Abelian

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]

/-- The unit of the constant sheaf adjunction at a terminal object `T`, evaluated at `1`, is
compatible with the restriction to any other terminal object `T'`. -/
lemma constantHomEquiv_id_congr {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') :
    constantHomEquiv hT' _ (𝟙 ((constantSheaf J AddCommGrpCat.{w}).obj
      (AddCommGrpCat.of (ULift ℤ)))) =
      ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))).obj.map
        (hT.from T').op (constantHomEquiv hT _ (𝟙 _)) := by
  have h : (constantSheafAdj J AddCommGrpCat.{w} hT').unit.app (AddCommGrpCat.of (ULift ℤ)) =
      (constantSheafAdj J AddCommGrpCat.{w} hT).unit.app (AddCommGrpCat.of (ULift ℤ)) ≫
        ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))).obj.map
          (hT.from T').op := by
    simp only [constantSheafAdj, Adjunction.comp_unit_app, Category.assoc]
    erw [← (toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{w} ℤ)))).naturality]
    simp [constantPresheafAdj]
  simp only [constantHomEquiv, Equiv.trans_apply, AddEquiv.toEquiv_eq_coe,
    Adjunction.homEquiv_unit, Functor.map_id, h]
  rfl

/-- Morphisms out of the constant sheaf `ℤ` are global sections, compatibly with the change of
the terminal object. -/
lemma constantHomEquiv_congr {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T')
    (F : Sheaf J AddCommGrpCat.{w})
    (f : (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) :
    constantHomEquiv hT' F f = F.obj.map (hT.from T').op (constantHomEquiv hT F f) := by
  rw [← constantHomEquiv_naturality hT f, ← constantHomEquiv_id_congr hT hT',
    ← constantHomEquiv_comp, Category.id_comp]

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- The identification `H⁰(F) ≅ F(T)` is compatible with the change of the terminal object. -/
lemma H.equiv₀_congr {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T')
    (F : Sheaf J AddCommGrpCat.{w}) (x : H F 0) :
    H.equiv₀ F hT' x = F.obj.map (hT.from T').op (H.equiv₀ F hT x) :=
  constantHomEquiv_congr hT hT' F (Ext.addEquiv₀ x)

/-- The connecting homomorphism `Γ(Q) → H¹(G)` is compatible with the change of the terminal
object. -/
lemma H.δ_congr {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T')
    {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact) (s : S.X₃.obj.obj (op T)) :
    H.δSections hS hT' (S.X₃.obj.map (hT.from T').op s) = H.δSections hS hT s := by
  obtain ⟨x, rfl⟩ := (H.equiv₀ S.X₃ hT).surjective s
  rw [← H.equiv₀_congr hT hT', ← H.δSucc_zero, ← H.δSucc_zero]

namespace Torsor

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{w})] {G : Sheaf J AddCommGrpCat.{w}}

omit [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] [EnoughInjectives (Sheaf J AddCommGrpCat.{w})] in
/-- The lifting torsor of a global section does not depend on the terminal object. -/
lemma lifts_equiv_lifts_congr {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T')
    {I Q : Sheaf J AddCommGrpCat.{w}} {ι : G ⟶ I} {d : I ⟶ Q} {w : ι ≫ d = 0}
    (hS : (ShortComplex.mk ι d w).ShortExact) (s : Q.obj.obj (op T)) :
    lifts hT hS s ≈ lifts hT' hS (Q.obj.map (hT.from T').op s) := by
  refine ⟨Iso.ofHom (ObjectProperty.homMk
    { app U := TypeCat.ofHom fun x ↦ ⟨x.1, ?_⟩
      naturality U V f := rfl }) fun U a x ↦ rfl⟩
  change d.hom.app U x.1 = Q.obj.map (hT'.from U.unop).op (Q.obj.map (hT.from T').op s)
  rw [lifts_val hT hS x, ← ConcreteCategory.comp_apply, ← Q.obj.map_comp, ← op_comp]
  exact congrArg (fun f ↦ Q.obj.map f.op s) (hT.hom_ext _ _)

/-- **The class of a torsor does not depend on the terminal object.** -/
theorem classH1_congr {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T') (P : Torsor G) :
    classH1 G hT' ⟦P⟧ = classH1 G hT ⟦P⟧ := by
  have hS := injectiveSequence_shortExact G
  obtain ⟨s, hs⟩ := exists_equiv_lifts hT hS P
  rw [_root_.Quotient.sound hs, classH1_lifts,
    _root_.Quotient.sound (lifts_equiv_lifts_congr hT hT' hS s), classH1_lifts]
  exact H.δ_congr hT hT' hS s

end Torsor

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Etale

open Scheme Sheaf

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- **Pullback in degree zero.** Under the identifications `H⁰(F) ≅ F(Y)` and
`H⁰(g^* F) ≅ (g^* F)(X)`, the pullback map on `H⁰` is the pullback of global sections along
the unit `F ⟶ g_* g^* F`, followed by the restriction along any morphism `X ⟶ Y ×_Y X` of
étale `X`-schemes; any terminal objects of the small étale sites may be used. -/
lemma equiv₀_cohomologyMap (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : H F 0) {TX : X.Etale} (hTX : IsTerminal TX) {TY : Y.Etale} (hTY : IsTerminal TY)
    (e : TX ⟶ g.Etale.obj TY) :
    H.equiv₀ _ hTX (cohomologyMap g F 0 x) =
      ((g)^*[AddCommGrpCat.{u + 1}].obj F).obj.map e.op
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app F).hom.app (op TY)
          (H.equiv₀ F hTY x)) := by
  let tY := terminalIsTerminal (C := Y.Etale)
  let tX := terminalIsTerminal (C := X.Etale)
  let ΓY := Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1} tY
  let ΓX := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1} tX
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g
  let y := H.equiv₀ F tY x
  have hx : x = (H.equiv₀ F tY).symm (ΓY.hom.app F (ΓY.inv.app F y)) := by
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app]
    exact ((H.equiv₀ F tY).symm_apply_apply x).symm
  have h₀ := cohomologyMap_zero_eq_globalSectionsUpperStarMap g F (ΓY.inv.app F y)
  rw [← hx] at h₀
  have h₁ : H.equiv₀ _ tX (cohomologyMap g F 0 x) =
      ((g)^*[AddCommGrpCat.{u + 1}].obj F).obj.map (PreservesTerminal.iso g.Etale).inv.op
        ((adj.unit.app F).hom.app (op (⊤_ Y.Etale)) y) := by
    have cX (z) : ΓX.hom.app ((g)^*[AddCommGrpCat.{u + 1}].obj F)
        (ΓX.inv.app ((g)^*[AddCommGrpCat.{u + 1}].obj F) z) = z := by
      rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app]
      rfl
    have cY (z) : ΓY.hom.app F (ΓY.inv.app F z) = z := by
      rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id_app]
      rfl
    rw [h₀, AddEquiv.apply_symm_apply]
    simp only [globalSectionsUpperStarMap, ConcreteCategory.comp_apply]
    erw [cX, cY]
    rfl
  have hT : IsTerminal (g.Etale.obj (⊤_ Y.Etale)) :=
    tX.ofIso (PreservesTerminal.iso g.Etale).symm
  have he : tX.from _ ≫ (PreservesTerminal.iso g.Etale).inv = e ≫ g.Etale.map (tY.from _) :=
    hT.hom_ext _ _
  rw [H.equiv₀_congr tX hTX, h₁, H.equiv₀_congr tY hTY]
  have hnat : (adj.unit.app F).hom.app (op TY) (F.obj.map (tY.from TY).op y) =
      ((g)^*[AddCommGrpCat.{u + 1}].obj F).obj.map (g.Etale.map (tY.from TY)).op
        ((adj.unit.app F).hom.app (op (⊤_ Y.Etale)) y) :=
    ConcreteCategory.congr_hom ((adj.unit.app F).hom.naturality (tY.from TY).op) y
  have hcomp {A B D : X.Etale} (a : A ⟶ B) (b : B ⟶ D)
      (z : ((g)^*[AddCommGrpCat.{u + 1}].obj F).obj.obj (op D)) :
      ((g)^*[AddCommGrpCat.{u + 1}].obj F).obj.map a.op
        (((g)^*[AddCommGrpCat.{u + 1}].obj F).obj.map b.op z) =
        ((g)^*[AddCommGrpCat.{u + 1}].obj F).obj.map (a ≫ b).op z := by
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  refine (hcomp _ _ _).trans ?_
  refine (congrArg (fun a ↦ ((g)^*[AddCommGrpCat.{u + 1}].obj F).obj.map a.op
    ((adj.unit.app F).hom.app (op (⊤_ Y.Etale)) y)) he).trans ?_
  exact ((hcomp _ _ _).symm.trans (congrArg _ hnat.symm))

variable {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}

/-- **Pullback in degree zero, with change of coefficients.** For `φ : G ⟶ g_* G'`, the map
`H⁰(Y, G) ⟶ H⁰(X, g^* G) ⟶ H⁰(X, G')` induced by the transpose `g^* G ⟶ G'` of `φ` is `φ` on
global sections, followed by the restriction along a morphism `X ⟶ Y ×_Y X` of étale
`X`-schemes. -/
lemma equiv₀_map_cohomologyMap (φ : G ⟶ (g)_*[AddCommGrpCat.{u + 1}].obj G') (x : H G 0)
    {TX : X.Etale} (hTX : IsTerminal TX) {TY : Y.Etale} (hTY : IsTerminal TY)
    (e : TX ⟶ g.Etale.obj TY) :
    H.equiv₀ G' hTX (H.map (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
        _ _).symm φ) 0 (cohomologyMap g G 0 x)) =
      G'.obj.map e.op (φ.hom.app (op TY) (H.equiv₀ G hTY x)) := by
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g
  let ψ : (g)^*[AddCommGrpCat.{u + 1}].obj G ⟶ G' := (adj.homEquiv _ _).symm φ
  have hφ : adj.homEquiv _ _ ψ = φ := Equiv.apply_symm_apply _ _
  rw [← H.equiv₀_naturality, equiv₀_cohomologyMap g G x hTX hTY e]
  refine (ConcreteCategory.congr_hom (ψ.hom.naturality e.op)
    ((adj.unit.app G).hom.app (op TY) (H.equiv₀ G hTY x))).trans ?_
  refine congrArg (G'.obj.map e.op) ?_
  rw [← hφ, Adjunction.homEquiv_unit]
  rfl

/-- **Pullback of torsors**, for arbitrary terminal objects of the small étale sites. See
`AlgebraicGeometry.Etale.classH1_eq_map_cohomologyMap_of_equivariant`. -/
theorem classH1_eq_map_cohomologyMap_of_equivariant'
    (φ : G ⟶ (g)_*[AddCommGrpCat.{u + 1}].obj G') (P : Torsor G) (P' : Torsor G')
    (σ : ∀ U : Y.Etaleᵒᵖ, P.sheaf.obj.obj U →
      P'.sheaf.obj.obj (op (g.Etale.obj U.unop)))
    (hσ : ∀ ⦃U V : Y.Etaleᵒᵖ⦄ (f : U ⟶ V) (x : P.sheaf.obj.obj U),
      P'.sheaf.obj.map (g.Etale.map f.unop).op (σ U x) =
        σ V (P.sheaf.obj.map f x))
    (hσ₁ : ∀ (U : Y.Etaleᵒᵖ) (a : G.obj.obj U) (x : P.sheaf.obj.obj U),
      σ U (P.vadd U a x) = P'.vadd (op (g.Etale.obj U.unop)) (φ.hom.app U a) (σ U x))
    {TX : X.Etale} (hTX : IsTerminal TX) {TY : Y.Etale} (hTY : IsTerminal TY) :
    Torsor.classH1 G' hTX ⟦P'⟧ =
      H.map (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _).symm φ) 1
        (cohomologyMap g G 1 (Torsor.classH1 G hTY ⟦P⟧)) := by
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g
  let gU := (g)^*[AddCommGrpCat.{u + 1}]
  let gL := (g)_*[AddCommGrpCat.{u + 1}]
  let ψ : gU.obj G ⟶ G' := (adj.homEquiv _ _).symm φ
  have hψ : adj.homEquiv _ _ ψ = φ := Equiv.apply_symm_apply _ _
  -- the injective resolutions and the lifting torsors
  let S := Torsor.injectiveSequence G
  let S' := Torsor.injectiveSequence G'
  have hS : S.ShortExact := Torsor.injectiveSequence_shortExact G
  have hS' : S'.ShortExact := Torsor.injectiveSequence_shortExact G'
  obtain ⟨s, hs⟩ := Torsor.exists_equiv_lifts hTY hS P
  obtain ⟨s', hs'⟩ := Torsor.exists_equiv_lifts hTX hS' P'
  -- the morphism of short exact sequences `g^* S ⟶ S'` over `ψ`
  have hgS : (S.map gU).ShortExact := hS.map_of_exact gU
  have : Mono (gU.map S.f) := hgS.mono_f
  let χ : gU.obj S.X₂ ⟶ S'.X₂ := Injective.factorThru (ψ ≫ S'.f) (gU.map S.f)
  have h₁ : gU.map S.f ≫ χ = ψ ≫ S'.f := Injective.comp_factorThru _ _
  let ψQ : gU.obj S.X₃ ⟶ S'.X₃ := hgS.gIsCokernel.desc (CokernelCofork.ofπ (χ ≫ S'.g) (by
    change gU.map S.f ≫ χ ≫ S'.g = 0
    rw [← Category.assoc, h₁, Category.assoc, S'.zero, comp_zero]))
  have h₂ : gU.map S.g ≫ ψQ = χ ≫ S'.g := hgS.gIsCokernel.fac _ WalkingParallelPair.one
  let m : S.map gU ⟶ S' :=
    { τ₁ := ψ
      τ₂ := χ
      τ₃ := ψQ
      comm₁₂ := h₁.symm
      comm₂₃ := h₂.symm }
  -- transposes
  let χ' : S.X₂ ⟶ gL.obj S'.X₂ := adj.homEquiv _ _ χ
  let ψQ' : S.X₃ ⟶ gL.obj S'.X₃ := adj.homEquiv _ _ ψQ
  have h₁' : S.f ≫ χ' = φ ≫ gL.map S'.f := by
    rw [← adj.homEquiv_naturality_left, h₁, adj.homEquiv_naturality_right, hψ]
  have h₂' : S.g ≫ ψQ' = χ' ≫ gL.map S'.g := by
    rw [← adj.homEquiv_naturality_left, h₂, adj.homEquiv_naturality_right]
  -- reduce to a statement about global sections
  rw [_root_.Quotient.sound hs, _root_.Quotient.sound hs', Torsor.classH1_lifts,
    Torsor.classH1_lifts]
  obtain ⟨x, rfl⟩ := (H.equiv₀ S.X₃ hTY).surjective s
  rw [← H.δSucc_zero hS hTY x, cohomologyMap_δSucc g hS 0 x]
  have key := H.map_δSucc hgS hS' m 0 (cohomologyMap g S.X₃ 0 x)
  refine Eq.trans ?_ key.symm
  rw [H.δSucc_zero hS' hTX, ← sub_eq_zero, ← map_sub, ← AddMonoidHom.mem_ker, H.ker_δ]
  have hT : IsTerminal (g.Etale.obj TY) :=
    (IsTerminal.isTerminalObj g.Etale TY hTY)
  let e : TX ⟶ g.Etale.obj TY := hT.from TX
  change s' - H.equiv₀ _ hTX (H.map ψQ 0 (cohomologyMap g S.X₃ 0 x)) ∈ _
  rw [← H.equiv₀_naturality, equiv₀_cohomologyMap g S.X₃ x hTX hTY e]
  set s := H.equiv₀ S.X₃ hTY x with hs_def
  -- the lifts of the local sections of `P` and `P'`
  obtain ⟨eP⟩ := hs
  obtain ⟨eP'⟩ := hs'
  let b (U : Y.Etaleᵒᵖ) (y : P.sheaf.obj.obj U) : S.X₂.obj.obj U := (eP.iso.hom.hom.app U y).1
  let b' (U : X.Etaleᵒᵖ) (y : P'.sheaf.obj.obj U) : S'.X₂.obj.obj U :=
    (eP'.iso.hom.hom.app U y).1
  have hb_nat {U V : Y.Etaleᵒᵖ} (f : U ⟶ V) (y) :
      S.X₂.obj.map f (b U y) = b V (P.sheaf.obj.map f y) := by
    have h := ConcreteCategory.congr_hom (eP.iso.hom.hom.naturality f) y
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    exact (congr_arg Subtype.val h).symm
  have hb'_nat {U V : X.Etaleᵒᵖ} (f : U ⟶ V) (y) :
      S'.X₂.obj.map f (b' U y) = b' V (P'.sheaf.obj.map f y) := by
    have h := ConcreteCategory.congr_hom (eP'.iso.hom.hom.naturality f) y
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    exact (congr_arg Subtype.val h).symm
  have hb_vadd (U a y) : b U (P.vadd U a y) = b U y + S.f.hom.app U a :=
    congr_arg Subtype.val (eP.map_vadd U a y)
  have hb'_vadd (U a y) : b' U (P'.vadd U a y) = b' U y + S'.f.hom.app U a :=
    congr_arg Subtype.val (eP'.map_vadd U a y)
  have hb_d (U y) : S.g.hom.app U (b U y) = S.X₃.obj.map (hTY.from U.unop).op s :=
    Torsor.lifts_val hTY hS (eP.iso.hom.hom.app U y)
  have hb'_d (U y) : S'.g.hom.app U (b' U y) = S'.X₃.obj.map (hTX.from U.unop).op s' :=
    Torsor.lifts_val hTX hS' (eP'.iso.hom.hom.app U y)
  -- the differences of the lifts glue to a section `c₀` of `I'` over `TY ×_Y X`
  let F := (sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj
    (gL.obj S'.X₂)
  let χa (U : Y.Etaleᵒᵖ) (z : S.X₂.obj.obj U) :
      S'.X₂.obj.obj (op (g.Etale.obj U.unop)) :=
    χ'.hom.app U z
  let c (U : Y.Etaleᵒᵖ) (y : P.sheaf.obj.obj U) : F.obj.obj U :=
    (b' (op (g.Etale.obj U.unop)) (σ U y) -
      χa U (b U y) : S'.X₂.obj.obj (op (g.Etale.obj
        U.unop)))
  have hχ'_nat {U V : Y.Etaleᵒᵖ} (f : U ⟶ V) (z : S.X₂.obj.obj U) :
      S'.X₂.obj.map (g.Etale.map f.unop).op
        (χa U z) = χa V (S.X₂.obj.map f z) :=
    (ConcreteCategory.congr_hom (χ'.hom.naturality f) z).symm
  have hχ'_f (U : Y.Etaleᵒᵖ) (a : G.obj.obj U) :
      χa U (S.f.hom.app U a) = S'.f.hom.app (op (g.Etale.obj U.unop)) (φ.hom.app U a) :=
    ConcreteCategory.congr_hom (congr_arg (fun k ↦ k.hom.app U) h₁') a
  have hc_nat : ∀ ⦃U V : Y.Etaleᵒᵖ⦄ (f : U ⟶ V) (y : P.sheaf.obj.obj U),
      F.obj.map f (c U y) = c V (P.sheaf.obj.map f y) := by
    intro U V f y
    change S'.X₂.obj.map (g.Etale.map f.unop).op
      (b' _ (σ U y) - χa U (b U y)) = b' _ (σ V (P.sheaf.obj.map f y)) -
        χa V (b V (P.sheaf.obj.map f y))
    rw [map_sub, hb'_nat, hσ, hχ'_nat, hb_nat]
  have hc_inv : ∀ (U : Y.Etaleᵒᵖ) (a : G.obj.obj U) (y : P.sheaf.obj.obj U),
      c U (P.vadd U a y) = c U y := by
    intro U a y
    change b' _ (σ U (P.vadd U a y)) - χa U (b U (P.vadd U a y)) =
      b' _ (σ U y) - χa U (b U y)
    rw [hσ₁]
    rw [hb'_vadd]
    have hadd (z w : S.X₂.obj.obj U) : χa U (z + w) = χa U z + χa U w := map_add _ z w
    rw [hb_vadd, hadd, hχ'_f]
    abel
  obtain ⟨c₀, hc₀⟩ := Torsor.exists_section_of_invariant P F hTY c hc_nat hc_inv
  -- `c₀` lifts `s' - ψ(g^* s)` over `TY ×_Y X`
  let FQ := (sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj
    (gL.obj S'.X₃)
  let ψa (U : Y.Etaleᵒᵖ) (z : S.X₃.obj.obj U) :
      S'.X₃.obj.obj (op (g.Etale.obj U.unop)) :=
    ψQ'.hom.app U z
  have hψa (U : Y.Etaleᵒᵖ) (z : S.X₃.obj.obj U) :
      ψa U z = ψQ.hom.app (op (g.Etale.obj U.unop)) ((adj.unit.app S.X₃).hom.app U z) := by
    simp only [ψa, ψQ', Adjunction.homEquiv_unit]
    rfl
  have hK : S'.g.hom.app (op (g.Etale.obj TY)) c₀ =
      S'.X₃.obj.map (hTX.from (g.Etale.obj TY)).op s' - ψa (op TY) s := by
    refine Torsor.ext_of_nonempty P FQ fun V f ⟨y⟩ ↦ ?_
    obtain rfl : f = hTY.from V := hTY.hom_ext _ _
    change S'.X₃.obj.map (g.Etale.map (hTY.from V)).op (S'.g.hom.app _ c₀) =
      S'.X₃.obj.map (g.Etale.map (hTY.from V)).op
        (S'.X₃.obj.map (hTX.from (g.Etale.obj TY)).op s' - ψa (op TY) s)
    have h1 : S'.X₂.obj.map (g.Etale.map (hTY.from V)).op c₀ = c (op V) y := (hc₀ (op V) y).symm
    have h2 (z : S.X₂.obj.obj (op V)) :
        S'.g.hom.app (op (g.Etale.obj V)) (χa (op V) z) = ψa (op V) (S.g.hom.app (op V) z) :=
      (ConcreteCategory.congr_hom (congr_arg (fun k ↦ k.hom.app (op V)) h₂') z).symm
    have h3 : ψa (op V) (S.X₃.obj.map (hTY.from V).op s) =
        S'.X₃.obj.map (g.Etale.map (hTY.from V)).op (ψa (op TY) s) :=
      ConcreteCategory.congr_hom (ψQ'.hom.naturality (hTY.from V).op) s
    have h4 : S'.X₃.obj.map (g.Etale.map (hTY.from V)).op
        (S'.X₃.obj.map (hTX.from (g.Etale.obj TY)).op s') =
          S'.X₃.obj.map (hTX.from (g.Etale.obj V)).op s' := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      exact congrArg (fun k ↦ S'.X₃.obj.map k.op s') (hTX.hom_ext _ _)
    have h5 : S'.X₃.obj.map (g.Etale.map (hTY.from V)).op (S'.g.hom.app _ c₀) =
        S'.g.hom.app _ (S'.X₂.obj.map (g.Etale.map (hTY.from V)).op c₀) :=
      (ConcreteCategory.congr_hom (S'.g.hom.naturality (g.Etale.map (hTY.from V)).op) c₀).symm
    rw [h5, h1]
    change S'.g.hom.app _ (b' _ (σ (op V) y) - χa (op V) (b (op V) y)) = _
    rw [map_sub, hb'_d, h2, hb_d, h3, map_sub, h4]
  refine ⟨S'.X₂.obj.map e.op c₀, ?_⟩
  have h6 : S'.g.hom.app (op TX) (S'.X₂.obj.map e.op c₀) =
      S'.X₃.obj.map e.op (S'.g.hom.app _ c₀) :=
    (ConcreteCategory.congr_hom (S'.g.hom.naturality e.op) c₀)
  have h7 : S'.X₃.obj.map e.op (S'.X₃.obj.map (hTX.from (g.Etale.obj TY)).op s') = s' := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      show e ≫ hTX.from _ = 𝟙 TX from hTX.hom_ext _ _, op_id, CategoryTheory.Functor.map_id]
    rfl
  have h8 : S'.X₃.obj.map e.op (ψa (op TY) s) = ψQ.hom.app (op TX)
      ((gU.obj S.X₃).obj.map e.op ((adj.unit.app S.X₃).hom.app (op TY) s)) := by
    rw [hψa]
    exact (ConcreteCategory.congr_hom (ψQ.hom.naturality e.op) _).symm
  change S'.g.hom.app (op TX) (S'.X₂.obj.map e.op c₀) = _
  rw [h6, hK, map_sub, h7, h8]

/-- **Pullback of torsors.** Let `g : X ⟶ Y`, `φ : G ⟶ g_* G'` a morphism of abelian sheaves,
`P` a `G`-torsor on `Y_ét` and `P'` a `G'`-torsor on `X_ét`, and let `σ : P(V) → P'(V ×_Y X)`
be maps, natural in the étale `Y`-scheme `V`, with `σ(a • x) = φ(a) • σ(x)`. Then the class of
`P'` in `H¹(X, G')` is the image of the class of `P` under the pullback map
`H¹(Y, G) ⟶ H¹(X, g^* G) ⟶ H¹(X, G')`, the second map being induced by the transpose
`g^* G ⟶ G'` of `φ`. -/
theorem classH1_eq_map_cohomologyMap_of_equivariant
    (φ : G ⟶ (g)_*[AddCommGrpCat.{u + 1}].obj G') (P : Torsor G) (P' : Torsor G')
    (σ : ∀ U : Y.Etaleᵒᵖ, P.sheaf.obj.obj U →
      P'.sheaf.obj.obj (op (g.Etale.obj U.unop)))
    (hσ : ∀ ⦃U V : Y.Etaleᵒᵖ⦄ (f : U ⟶ V) (x : P.sheaf.obj.obj U),
      P'.sheaf.obj.map (g.Etale.map f.unop).op (σ U x) =
        σ V (P.sheaf.obj.map f x))
    (hσ₁ : ∀ (U : Y.Etaleᵒᵖ) (a : G.obj.obj U) (x : P.sheaf.obj.obj U),
      σ U (P.vadd U a x) = P'.vadd (op (g.Etale.obj U.unop)) (φ.hom.app U a) (σ U x)) :
    Torsor.classH1 G' (isTerminalEtale X) ⟦P'⟧ =
      H.map (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv _ _).symm φ) 1
        (cohomologyMap g G 1 (Torsor.classH1 G (isTerminalEtale Y) ⟦P⟧)) :=
  classH1_eq_map_cohomologyMap_of_equivariant' g φ P P' σ hσ hσ₁ _ _

end AlgebraicGeometry.Etale
