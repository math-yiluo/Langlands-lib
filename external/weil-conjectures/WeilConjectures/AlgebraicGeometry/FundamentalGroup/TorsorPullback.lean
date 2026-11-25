/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Extension
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor

/-!
# Base change of torsors and the induced map on fundamental groups

Let `f : X ⟶ Y` be a morphism of connected schemes, `s` a geometric point of `X` and `t = s ≫ f`.
The base change `P ×_Y X` of an `M`-torsor `P` over `Y` is an `M`-torsor over `X`
(`AlgebraicGeometry.Scheme.EtaleTorsor.pullback`), and its monodromy character is that of `P`
composed with the induced map `ρ : π₁(X, s) → π₁(Y, t)`
(`AlgebraicGeometry.Scheme.EtaleTorsor.monodromy_pullback`). Consequently, if `ρ` is surjective,
torsors over `Y` are determined by their base changes
(`AlgebraicGeometry.Scheme.EtaleTorsor.isIsomorphic_of_isIsomorphic_pullback`), and a torsor over
`X` whose monodromy character kills the kernel of `ρ` is the base change of a torsor over `Y`
(`AlgebraicGeometry.Scheme.EtaleTorsor.exists_isIsomorphic_pullback`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.EtaleTorsor

open FiniteEtale

variable {M : Type (u + 1)} [AddCommGroup M] [Finite M] {X Y : Scheme.{u}} (f : X ⟶ Y)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

/-- The geometric fibres of the base change of an `M`-torsor are `M`-torsors. -/
lemma existsUnique_fiber_map_pullback_map_vaddHom (t : EtaleTorsor M Y)
    (x y : (fiber s).obj ((FiniteEtale.pullback f).obj t.toFiniteEtale)) :
    ∃! m, (fiber s).map ((FiniteEtale.pullback f).map (t.vaddHom m)) x = y := by
  let τ := pullbackFiberIso f s
  have hτ (m : M) (z : (fiber s).obj ((FiniteEtale.pullback f).obj t.toFiniteEtale)) :
      τ.hom.app _ ((fiber s).map ((FiniteEtale.pullback f).map (t.vaddHom m)) z) =
        (fiber (s ≫ f)).map (t.vaddHom m) (τ.hom.app _ z) :=
    ConcreteCategory.congr_hom (τ.hom.naturality (t.vaddHom m)) z
  have hinj : Function.Injective (τ.hom.app t.toFiniteEtale) :=
    (ConcreteCategory.bijective_of_isIso (τ.hom.app t.toFiniteEtale)).1
  obtain ⟨m, hm, huniq⟩ := t.existsUnique_fiber_map_vaddHom (s ≫ f) (τ.hom.app _ x)
    (τ.hom.app _ y)
  exact ⟨m, hinj (by rw [hτ, hm]), fun n hn ↦ huniq n (by beta_reduce; rw [← hτ, hn])⟩

variable [ConnectedSpace X]

/-- The base change `P ×_Y X` of an `M`-torsor `P` over `Y` along `f : X ⟶ Y`, with the action of
`M` on the first factor. The action is simply transitive since it is so on the geometric fibre
at any geometric point of the connected, hence nonempty, scheme `X`. -/
noncomputable def pullback (t : EtaleTorsor M Y) : EtaleTorsor M X where
  P := Limits.pullback t.π f
  π := Limits.pullback.snd t.π f
  isFinite := by have := t.isFinite; infer_instance
  etale := by have := t.etale; infer_instance
  surjective := by have := t.surjective; infer_instance
  vadd m := ((FiniteEtale.pullback f).map (t.vaddHom m)).hom.left
  vadd_π m := hom_left_comp ((FiniteEtale.pullback f).map (t.vaddHom m))
  zero_vadd := by rw [vaddHom_zero, CategoryTheory.Functor.map_id]; rfl
  add_vadd m n := by rw [vaddHom_add, Functor.map_comp]; rfl
  isIso_sigmaDesc := by
    obtain ⟨x⟩ := ConnectedSpace.toNonempty (α := X)
    let s' : Spec (.of (AlgebraicClosure (X.residueField x))) ⟶ X :=
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))) ≫
        X.fromSpecResidueField x
    exact isIso_sigmaDesc_of_existsUnique s' ((FiniteEtale.pullback f).obj t.toFiniteEtale)
      (fun m ↦ (FiniteEtale.pullback f).map (t.vaddHom m))
      (existsUnique_fiber_map_pullback_map_vaddHom f s' t)

variable (t : EtaleTorsor M Y)

lemma toFiniteEtale_pullback :
    (t.pullback f).toFiniteEtale = (FiniteEtale.pullback f).obj t.toFiniteEtale :=
  rfl


@[simp]
lemma pullback_P : (t.pullback f).P = Limits.pullback t.π f :=
  rfl

@[simp]
lemma pullback_π : (t.pullback f).π = Limits.pullback.snd t.π f :=
  rfl

lemma pullback_vadd (m : M) :
    (t.pullback f).vadd m = Limits.pullback.map t.π f t.π f (t.vadd m) (𝟙 X) (𝟙 Y)
      (by rw [Category.comp_id, t.vadd_π]) (by rw [Category.comp_id, Category.id_comp]) :=
  rfl

lemma vaddHom_pullback (m : M) :
    (t.pullback f).vaddHom m = (FiniteEtale.pullback f).map (t.vaddHom m) :=
  rfl

/-- Isomorphic torsors are isomorphic as finite étale schemes. -/
lemma IsIsomorphic.nonempty_iso {Z : Scheme.{u}} {t₁ t₂ : EtaleTorsor M Z}
    (h : t₁.IsIsomorphic t₂) :
    Nonempty (t₁.toFiniteEtale ≅ t₂.toFiniteEtale) := by
  obtain ⟨φ, hπ, -⟩ := h
  exact ⟨{ hom := ObjectProperty.homMk (MorphismProperty.Over.homMk φ.hom hπ)
           inv := ObjectProperty.homMk (MorphismProperty.Over.homMk φ.inv (by
             change φ.inv ≫ t₁.π = t₂.π
             rw [← hπ, ← Category.assoc, φ.inv_hom_id, Category.id_comp]))
           hom_inv_id := FiniteEtale.hom_ext φ.hom_inv_id
           inv_hom_id := FiniteEtale.hom_ext φ.inv_hom_id }⟩

/-- Base change preserves isomorphism of torsors. -/
lemma IsIsomorphic.pullback {t₁ t₂ : EtaleTorsor M Y} (h : t₁.IsIsomorphic t₂) :
    (t₁.pullback f).IsIsomorphic (t₂.pullback f) := by
  obtain ⟨φ, hπ, hv⟩ := h
  let Φ : t₁.toFiniteEtale ≅ t₂.toFiniteEtale :=
    { hom := ObjectProperty.homMk (MorphismProperty.Over.homMk φ.hom hπ)
      inv := ObjectProperty.homMk (MorphismProperty.Over.homMk φ.inv (by
        change φ.inv ≫ t₁.π = t₂.π
        rw [← hπ, ← Category.assoc, φ.inv_hom_id, Category.id_comp]))
      hom_inv_id := FiniteEtale.hom_ext φ.hom_inv_id
      inv_hom_id := FiniteEtale.hom_ext φ.inv_hom_id }
  have hΦ (m : M) : t₁.vaddHom m ≫ Φ.hom = Φ.hom ≫ t₂.vaddHom m := FiniteEtale.hom_ext (hv m)
  let Ψ := (FiniteEtale.pullback f).mapIso Φ
  refine ⟨⟨Ψ.hom.hom.left, Ψ.inv.hom.left, congrArg (fun g ↦ g.hom.left) Ψ.hom_inv_id,
    congrArg (fun g ↦ g.hom.left) Ψ.inv_hom_id⟩, hom_left_comp Ψ.hom, fun m ↦ ?_⟩
  have := congrArg (FiniteEtale.pullback f).map (hΦ m)
  simp only [Functor.map_comp] at this
  exact congrArg (fun g ↦ g.hom.left) this

section Monodromy

open scoped FintypeCatDiscrete

variable [ConnectedSpace Y] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
  (G' : Type u) [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [CompactSpace G']
  [∀ P, MulAction G' ((fiber (s ≫ f)).obj P)] [IsFundamentalGroup (fiber (s ≫ f)) G']
  [TopologicalSpace M] [DiscreteTopology M]

/-- The monodromy character of the base change of a torsor `P` along `f` is that of `P` composed
with the induced map `π₁(X, s) → π₁(Y, s ≫ f)`. -/
lemma monodromy_pullback (g : G) :
    (t.pullback f).monodromy s G g =
      t.monodromy (s ≫ f) G' (fundamentalGroupMap (pullbackFiberIso f s) G G' g) := by
  let τ := pullbackFiberIso f s
  have hinj : Function.Injective (τ.hom.app t.toFiniteEtale) :=
    (ConcreteCategory.bijective_of_isIso (τ.hom.app t.toFiniteEtale)).1
  let x := ((t.pullback f).nonempty_fiber s).some
  refine ((t.pullback f).monodromy_eq_iff s G g x _).mpr (hinj ?_)
  have hτ := ConcreteCategory.congr_hom (τ.hom.naturality
    (t.vaddHom (t.monodromy (s ≫ f) G' (fundamentalGroupMap τ G G' g)).toAdd)) x
  simp only [Functor.comp_map, ConcreteCategory.comp_apply] at hτ
  rw [vaddHom_pullback]
  refine hτ.trans ?_
  rw [t.fiber_map_vaddHom_monodromy (s ≫ f) G']
  exact fundamentalGroupMap_smul τ G G' g t.toFiniteEtale x

variable {G G'}

/-- If `π₁(X, s) → π₁(Y, s ≫ f)` is surjective, torsors over `Y` with isomorphic base changes
are isomorphic. -/
lemma isIsomorphic_of_isIsomorphic_pullback
    (hρ : Function.Surjective (fundamentalGroupMap (pullbackFiberIso f s) G G'))
    {t₁ t₂ : EtaleTorsor M Y} (h : (t₁.pullback f).IsIsomorphic (t₂.pullback f)) :
    t₁.IsIsomorphic t₂ := by
  refine isIsomorphic_of_monodromy_eq (s ≫ f) G' (ContinuousMonoidHom.ext fun g' ↦ ?_)
  obtain ⟨g, rfl⟩ := hρ g'
  rw [← monodromy_pullback, ← monodromy_pullback, monodromy_eq_of_isIsomorphic s G h]

/-- If `π₁(X, s) → π₁(Y, s ≫ f)` is surjective, a torsor over `X` whose monodromy character is
trivial on the kernel of this map is isomorphic to the base change of a torsor over `Y`. -/
lemma exists_isIsomorphic_pullback
    (hρ : Function.Surjective (fundamentalGroupMap (pullbackFiberIso f s) G G'))
    (t : EtaleTorsor M X) (ht : ∀ g ∈ fixingSubgroup s f G, t.monodromy s G g = 1) :
    ∃ T : EtaleTorsor M Y, (T.pullback f).IsIsomorphic t := by
  let ρ := fundamentalGroupMap (pullbackFiberIso f s) G G'
  let χ := t.monodromy s G
  have hker : ρ.ker = fixingSubgroup s f G := ker_fundamentalGroupMap s f G _ G'
  have hχ (a b : G) (h : ρ a = ρ b) : χ a = χ b := by
    have hab : a⁻¹ * b ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [hker] at hab
    have := ht _ hab
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this
  let σ := Function.surjInv hρ
  have hσ (g : G) : χ (σ (ρ g)) = χ g := hχ _ _ (Function.surjInv_eq hρ _)
  have : ∀ P, ContinuousSMul G ((fiber s).obj P) := fun P ↦ IsFundamentalGroup.continuous_smul P
  have hc : Continuous ρ := continuous_fundamentalGroupMap (pullbackFiberIso f s) G G'
  have : T2Space G' := (toAutHomeo (fiber (s ≫ f)) G').isEmbedding.t2Space
  have hq : Topology.IsQuotientMap ρ := hc.isClosedMap.isQuotientMap hc hρ
  let χ' : G' →ₜ* Multiplicative M :=
    { toFun g' := χ (σ g')
      map_one' := by rw [← map_one ρ, hσ, map_one]
      map_mul' a b := by
        obtain ⟨a, rfl⟩ := hρ a
        obtain ⟨b, rfl⟩ := hρ b
        rw [← map_mul, hσ, hσ, hσ, map_mul]
      continuous_toFun := by
        rw [hq.continuous_iff]
        exact χ.continuous.congr fun g ↦ (hσ g).symm }
  obtain ⟨T, hT⟩ := exists_monodromy_eq (s ≫ f) G' χ'
  refine ⟨T, isIsomorphic_of_monodromy_eq s G (ContinuousMonoidHom.ext fun g ↦ ?_)⟩
  rw [monodromy_pullback f s T G G', hT]
  exact hσ g

end Monodromy

end AlgebraicGeometry.Scheme.EtaleTorsor
