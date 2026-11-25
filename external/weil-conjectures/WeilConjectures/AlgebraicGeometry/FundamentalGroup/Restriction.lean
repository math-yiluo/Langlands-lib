/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantCover
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
public import WeilConjectures.Mathlib.CategoryTheory.Galois.IsFundamentalgroup

/-!
# Maps of étale fundamental groups

Let `f : X ⟶ Y` be a morphism of connected schemes, `s` a geometric point of `X` and `t` one of
`Y`. Base change of finite étale covers along `f` and a path `τ : F_s ∘ f^* ≅ F_t` induce a
continuous homomorphism `π₁(X, s) → π₁(Y, t)`
(`AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap`), characterised by
`ρ(g) • τ y = τ (g • y)`. Such a path exists: the fibre functor `F_s ∘ f^*` is canonically
isomorphic to the fibre functor at `s ≫ f`
(`AlgebraicGeometry.Scheme.FiniteEtale.pullbackFiberIso`), and any two fibre functors are
isomorphic.

The map is surjective as soon as `f^*` carries connected covers to connected ones
(`AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap_surjective`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω']
  [IsSepClosed Ω'] (s : Spec (.of Ω) ⟶ X) (t : Spec (.of Ω') ⟶ Y)

/-- The geometric fibre at `s` of the base change `P ×_Y X` is the geometric fibre of `P` at
`s ≫ f`. -/
noncomputable def pullbackFiberIso : pullback f ⋙ fiber s ≅ fiber (s ≫ f) :=
  NatIso.ofComponents (fun P ↦ FintypeCat.equivEquivIso
    { toFun y := fiberMk (s ≫ f) P (y.left ≫ Limits.pullback.fst P.obj.hom f) (by
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
        exact congrArg (· ≫ f) (fiber_left_comp s y))
      invFun z := fiberMk s ((pullback f).obj P)
        (Limits.pullback.lift z.left s (fiber_left_comp _ z)) (Limits.pullback.lift_snd _ _ _)
      left_inv y := fiber_ext s (Limits.pullback.hom_ext (by simp)
        (by simpa using (fiber_left_comp s y).symm))
      right_inv z := fiber_ext _ (by simp) })
    (fun {P Q} φ ↦ by
      ext y
      apply fiber_ext
      change (y.left ≫ ((pullback f).map φ).hom.left) ≫ Limits.pullback.fst Q.obj.hom f =
        (y.left ≫ Limits.pullback.fst P.obj.hom f) ≫ φ.hom.left
      simp)

@[simp]
lemma pullbackFiberIso_hom_app_left (P : Y.FiniteEtale) (y : (fiber s).obj ((pullback f).obj P)) :
    ((pullbackFiberIso f s).hom.app P y).left = y.left ≫ Limits.pullback.fst P.obj.hom f :=
  rfl

variable {f s t} (τ : pullback f ⋙ fiber s ≅ fiber t) (GX : Type u) [Group GX]
  [∀ P, MulAction GX ((fiber s).obj P)]

/-- The action of `π₁(X, s)` on the geometric fibres at `t` of finite étale `Y`-schemes,
transported along a path `τ : F_s ∘ f^* ≅ F_t`. -/
@[instance_reducible]
noncomputable def transportMulAction (P : Y.FiniteEtale) : MulAction GX ((fiber t).obj P) where
  smul g z := τ.hom.app P (g • (show (fiber s).obj ((pullback f).obj P) from τ.inv.app P z))
  one_smul z := by
    change τ.hom.app P ((1 : GX) •
      (show (fiber s).obj ((pullback f).obj P) from τ.inv.app P z)) = z
    rw [one_smul]
    exact ConcreteCategory.congr_hom (τ.inv_hom_id_app P) z
  mul_smul g h z := by
    change τ.hom.app P ((g * h) • (show (fiber s).obj ((pullback f).obj P) from τ.inv.app P z)) =
      τ.hom.app P (g • (show (fiber s).obj ((pullback f).obj P) from τ.inv.app P
        (τ.hom.app P (h • (show (fiber s).obj ((pullback f).obj P) from τ.inv.app P z)))))
    rw [mul_smul]
    congr 2
    exact (ConcreteCategory.congr_hom (τ.hom_inv_id_app P) _).symm

lemma transportMulAction_smul (P : Y.FiniteEtale) (g : GX)
    (y : (fiber s).obj ((pullback f).obj P)) :
    letI := transportMulAction τ GX P
    g • τ.hom.app P y = τ.hom.app P (g • y) := by
  change τ.hom.app P (g • (show (fiber s).obj ((pullback f).obj P) from
    τ.inv.app P (τ.hom.app P y))) = _
  congr 2
  exact ConcreteCategory.congr_hom (τ.hom_inv_id_app P) y

variable [IsNaturalSMul (fiber s) GX]

lemma isNaturalSMul_transportMulAction :
    letI := fun P ↦ transportMulAction τ GX P
    IsNaturalSMul (fiber t) GX := by
  let := fun P ↦ transportMulAction τ GX P
  refine ⟨fun g P Q φ z ↦ ?_⟩
  obtain ⟨y, rfl⟩ : ∃ y : (fiber s).obj ((pullback f).obj P), τ.hom.app P y = z :=
    ⟨τ.inv.app P z, ConcreteCategory.congr_hom (τ.inv_hom_id_app P) z⟩
  have hn (w : (fiber s).obj ((pullback f).obj P)) : (fiber t).map φ (τ.hom.app P w) =
      τ.hom.app Q ((fiber s).map ((pullback f).map φ) w) :=
    (ConcreteCategory.congr_hom (τ.hom.naturality φ) w).symm
  rw [transportMulAction_smul, hn, hn, IsNaturalSMul.naturality, transportMulAction_smul]

section

variable [ConnectedSpace Y] (GY : Type u) [Group GY] [TopologicalSpace GY] [IsTopologicalGroup GY]
  [CompactSpace GY] [∀ P, MulAction GY ((fiber t).obj P)] [IsFundamentalGroup (fiber t) GY]

/-- The homomorphism `π₁(X, s) → π₁(Y, t)` induced by base change of finite étale covers along
`f : X ⟶ Y` and a path `τ : F_s ∘ f^* ≅ F_t`. -/
noncomputable def fundamentalGroupMap : GX →* GY :=
  letI := fun P ↦ transportMulAction τ GX P
  letI := isNaturalSMul_transportMulAction τ GX
  (toAutMulEquiv (fiber t) GY).symm.toMonoidHom.comp (toAut (fiber t) GX)

/-- The induced map of fundamental groups is characterised by `ρ(g) • τ y = τ (g • y)`. -/
lemma fundamentalGroupMap_smul (g : GX) (P : Y.FiniteEtale)
    (y : (fiber s).obj ((pullback f).obj P)) :
    fundamentalGroupMap τ GX GY g • τ.hom.app P y = τ.hom.app P (g • y) := by
  let := fun P ↦ transportMulAction τ GX P
  have := isNaturalSMul_transportMulAction τ GX
  rw [← toAut_hom_app_apply (F := fiber t) (G := GY)]
  change ((toAutMulEquiv (fiber t) GY) ((toAutMulEquiv (fiber t) GY).symm
    (toAut (fiber t) GX g))).asIso.hom.app P _ = _
  rw [MulEquiv.apply_symm_apply, toAut_hom_app_apply, transportMulAction_smul]

/-- The induced map of fundamental groups is continuous. -/
lemma continuous_fundamentalGroupMap [TopologicalSpace GX] [IsTopologicalGroup GX]
    [∀ P, ContinuousSMul GX ((fiber s).obj P)] :
    Continuous (fundamentalGroupMap τ GX GY) := by
  let := fun P ↦ transportMulAction τ GX P
  have := isNaturalSMul_transportMulAction τ GX
  have (P : Y.FiniteEtale) : ContinuousSMul GX ((fiber t).obj P) := by
    refine ⟨?_⟩
    change Continuous fun p : GX × (fiber t).obj P ↦ τ.hom.app P
      (p.1 • (show (fiber s).obj ((pullback f).obj P) from τ.inv.app P p.2))
    have h1 : Continuous fun p : GX × (fiber t).obj P ↦
        ((p.1, τ.inv.app P p.2) : GX × (fiber s).obj ((pullback f).obj P)) :=
      continuous_fst.prodMk (continuous_of_discreteTopology.comp continuous_snd)
    exact continuous_of_discreteTopology.comp (continuous_smul.comp h1)
  exact (toAutHomeo (fiber t) GY).symm.continuous.comp (toAut_continuous (fiber t) GX)

end

section

variable [ConnectedSpace Y] (GY : Type u) [Group GY] [TopologicalSpace GY] [IsTopologicalGroup GY]
  [CompactSpace GY] [∀ P, MulAction GY ((fiber t).obj P)] [IsFundamentalGroup (fiber t) GY]
  (GX : Type u) [Group GX] [∀ P, MulAction GX ((fiber s).obj P)]

/-- The map of fundamental groups induced by `f : X ⟶ Y` is surjective as soon as base change
along `f` carries connected finite étale covers to connected ones. -/
lemma fundamentalGroupMap_surjective [TopologicalSpace GX] [IsTopologicalGroup GX] [CompactSpace GX]
    [ConnectedSpace X] [IsFundamentalGroup (fiber s) GX]
    (h : ∀ P : Y.FiniteEtale, IsConnected P → IsConnected ((pullback f).obj P)) :
    Function.Surjective (fundamentalGroupMap τ GX GY) := by
  have : ∀ P, ContinuousSMul GX ((fiber s).obj P) := fun P ↦ IsFundamentalGroup.continuous_smul P
  refine surjective_of_forall_exists_smul_eq (fiber t) GY _ (continuous_fundamentalGroupMap τ GX GY)
    fun P _ x y ↦ ?_
  have := h P inferInstance
  obtain ⟨x', rfl⟩ : ∃ x' : (fiber s).obj ((pullback f).obj P), τ.hom.app P x' = x :=
    ⟨τ.inv.app P x, ConcreteCategory.congr_hom (τ.inv_hom_id_app P) x⟩
  obtain ⟨y', rfl⟩ : ∃ y' : (fiber s).obj ((pullback f).obj P), τ.hom.app P y' = y :=
    ⟨τ.inv.app P y, ConcreteCategory.congr_hom (τ.inv_hom_id_app P) y⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GX x' y'
  exact ⟨g, by rw [fundamentalGroupMap_smul, hg]⟩


/-- The map of fundamental groups induced by a finite étale morphism `f : X ⟶ Y` is injective:
a finite étale `X`-scheme `Q` is a finite étale `Y`-scheme through `f`, and `Q` embeds into the
base change of the latter along `f`, so an element acting trivially on all base changes acts
trivially on all finite étale `X`-schemes. -/
lemma fundamentalGroupMap_injective [IsFinite f] [Etale f] [ConnectedSpace X]
    [TopologicalSpace GX] [IsTopologicalGroup GX] [CompactSpace GX]
    [IsFundamentalGroup (fiber s) GX] :
    Function.Injective (fundamentalGroupMap τ GX GY) := by
  refine (injective_iff_map_eq_one _).2 fun g hg ↦ IsFundamentalGroup.non_trivial (F := fiber s)
    g fun Q y ↦ ?_
  have : IsFinite Q.obj.hom := Q.property
  have : Etale Q.obj.hom := Q.obj.prop
  let P : Y.FiniteEtale := ⟨MorphismProperty.Over.mk ⊤ (Q.obj.hom ≫ f) inferInstance,
    inferInstanceAs (IsFinite (Q.obj.hom ≫ f))⟩
  let φ : Q ⟶ (pullback f).obj P := ObjectProperty.homMk (MorphismProperty.Over.homMk
    (Limits.pullback.lift (𝟙 Q.obj.left) Q.obj.hom (by simp [P])) (Limits.pullback.lift_snd _ _ _))
  have htriv (z : (fiber s).obj ((pullback f).obj P)) : g • z = z := by
    have h := fundamentalGroupMap_smul τ GX GY g P z
    rw [hg, one_smul] at h
    exact ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1 h.symm
  have hinj : Function.Injective ((fiber s).map φ) := fun a b hab ↦ fiber_ext s (by
    have := congrArg (fun z ↦ z.left ≫ Limits.pullback.fst (Q.obj.hom ≫ f) f) hab
    simp only [fiber_map_left] at this
    change (a.left ≫ Limits.pullback.lift _ _ _) ≫ _ = (b.left ≫ Limits.pullback.lift _ _ _) ≫ _
      at this
    rw [Category.assoc, Category.assoc] at this
    erw [Limits.pullback.lift_fst] at this
    simpa using this)
  apply hinj
  rw [IsNaturalSMul.naturality, htriv]

end

section OpenImmersion

variable {U C : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j]

/-- The restriction to a nonempty open `U` of a finite étale `C`-scheme whose underlying scheme
is irreducible is connected: it is a nonempty open subscheme. -/
lemma isConnected_pullback_of_irreducibleSpace [ConnectedSpace U] [ConnectedSpace C]
    (P : C.FiniteEtale) [IsConnected P] [IrreducibleSpace P.obj.left] :
    IsConnected ((pullback j).obj P) := by
  have : ConnectedSpace ((pullback j).obj P).obj.left := by
    let g : ((pullback j).obj P).obj.left ⟶ P.obj.left := Limits.pullback.fst P.obj.hom j
    let q : P.obj.left ⟶ C := P.obj.hom
    have hP : Function.Surjective q := by
      obtain ⟨x⟩ := (inferInstance : Nonempty P.obj.left)
      have : IsFinite q := P.property
      have : Etale q := P.obj.prop
      have hc : IsClopen (Set.range q) := ⟨q.isClosedMap.isClosed_range, q.isOpenMap.isOpen_range⟩
      exact Set.range_eq_univ.1 (hc.eq_univ ⟨_, x, rfl⟩)
    obtain ⟨u⟩ := (inferInstance : Nonempty U)
    obtain ⟨x, hx⟩ := hP (j u)
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x u hx
    have hpre : IsPreirreducible (Set.univ : Set ((pullback j).obj P).obj.left) := by
      rw [← Set.preimage_univ (f := g)]
      exact (IrreducibleSpace.isIrreducible_univ _).isPreirreducible
        |>.preimage_of_isPreirreducible_fiber _ g.isOpenMap fun x ↦
          (Set.subsingleton_singleton.preimage g.isOpenEmbedding.injective).isPreirreducible
    have : PreirreducibleSpace ((pullback j).obj P).obj.left := ⟨hpre⟩
    have : IrreducibleSpace ((pullback j).obj P).obj.left := { toNonempty := ⟨z⟩ }
    infer_instance
  exact isConnected_of_connectedSpace ((pullback j).obj P)

end OpenImmersion

end AlgebraicGeometry.Scheme.FiniteEtale
