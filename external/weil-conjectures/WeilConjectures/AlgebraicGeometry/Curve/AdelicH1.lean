/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.ResidueSequence
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Cohomology of a module on a curve via principal parts at closed points

Let `X` be an integral noetherian scheme of dimension at most one over a field `k` (for instance
a smooth proper connected curve), with function field `K` and generic point `η`. Let
`φ : M ⟶ V_η` be a morphism from an `𝒪_X`-module `M` to the constant sheaf with value a
`K`-vector space `V`, injective on sections, and such that every `v ∈ V` is the value of a section
of `M` over some nonempty open (`M = 𝒪_X`, `V = K`; or `M = Ω¹_{X/k}`, `V = Ω[K⁄k]`).
Write `V_x ⊆ V` for the `k`-subspace `AlgebraicGeometry.Scheme.Modules.stalkLattice k φ x`.

The residue sequence `0 ⟶ M ⟶ V_η ⟶ 𝒫 ⟶ 0`
(`AlgebraicGeometry.Scheme.Modules.shortExact_residue`) then gives canonical `k`-linear
isomorphisms
```
  H¹(X, M) ≅ (⨁_{x closed} V ⧸ V_x) ⧸ V,        H⁰(X, M) ≅ ⋂_{x closed} V_x.
```
Every `v ∈ V` lies in `V_x` for all but finitely many closed points `x`, which defines the
diagonal map `V → ⨁_x V ⧸ V_x` (`AlgebraicGeometry.Scheme.Modules.principalPartsMap`).

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.principalPartsMap`: the map `V → ⨁_{x closed} V ⧸ V_x`.
- `AlgebraicGeometry.Scheme.Modules.adelicH1Equiv`: `H¹(X, M) ≃ₗ[k] (⨁_x V ⧸ V_x) ⧸ V`.
- `AlgebraicGeometry.Scheme.Modules.adelicH0Equiv`: `H⁰(X, M) ≃ₗ[k] ⋂_x V_x`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`)
-/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite TopologicalSpace

/-- A dependent function with finite support, as an element of `Π₀ i, β i`. -/
noncomputable def DFinsupp.mkOfFiniteSupport {ι : Type*} {β : ι → Type*} [∀ i, Zero (β i)]
    (f : ∀ i, β i)
    (hf : {i | f i ≠ 0}.Finite) : Π₀ i, β i :=
  ⟨f, Trunc.mk ⟨hf.toFinset.val, fun i ↦ (em (f i = 0)).elim Or.inr fun h ↦
    Or.inl (by simpa using h)⟩⟩

@[simp]
lemma DFinsupp.mkOfFiniteSupport_apply {ι : Type*} {β : ι → Type*} [∀ i, Zero (β i)]
    (f : ∀ i, β i) (hf : {i | f i ≠ 0}.Finite) (i : ι) : mkOfFiniteSupport f hf i = f i :=
  rfl

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- On an irreducible scheme of dimension at most one, every point other than the generic point
is closed. -/
lemma isClosed_singleton_of_ne_genericPoint [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 1) {x : X} (hx : x ≠ genericPoint X) : IsClosed {x} := by
  have hη : genericPoint X ∈ (closure {x})ᶜ := by
    intro h
    refine hx ((IsGenericPoint.eq ?_ (genericPoint_spec X)))
    rw [isGenericPoint_def]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec X).def]
    exact closure_minimal (Set.singleton_subset_iff.2 h) isClosed_closure
  exact isClosed_closure.isOpen_compl.isClosed_singleton_of_mem_compl hdim ⟨_, hη⟩
    fun h ↦ h (subset_closure rfl)

namespace Modules

variable [IsIntegral X] (k : Type u) [Field k] [X.Over (Spec (.of k))]
  [Algebra k X.functionField] [IsFunctionFieldAlgebra k X]
  {V : Type u} [AddCommGroup V] [Module X.functionField V] [Module k V]
  [IsScalarTower k X.functionField V] {M : X.Modules} (φ : M ⟶ skyscraper (genericPoint X) V)

section Finiteness

variable (hdim : topologicalKrullDim X ≤ 1)
  (hgen : ∀ v : V, v ∈ stalkLattice k φ (genericPoint X))

include hgen in
/-- Every `v ∈ V` lies in `V_x` for all `x` in a nonempty open. -/
lemma exists_isOpen_forall_mem_stalkLattice (v : V) :
    ∃ U : X.Opens, genericPoint X ∈ U ∧ ∀ x ∈ U, v ∈ stalkLattice k φ x := by
  obtain ⟨U, hU, s, rfl⟩ := hgen v
  exact ⟨U, hU, fun x hx ↦ ⟨U, hx, s, rfl⟩⟩

include hgen in
lemma subsingleton_quotient_stalkLattice_genericPoint :
    Subsingleton (V ⧸ stalkLattice k φ (genericPoint X)) := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  exact fun v _ ↦ hgen v

include hdim hgen in
/-- The points `x` with `v ∉ V_x` are closed. -/
lemma isClosed_singleton_of_not_mem_stalkLattice {v : V} {x : X}
    (hx : v ∉ stalkLattice k φ x) : IsClosed {x} :=
  isClosed_singleton_of_ne_genericPoint hdim fun h ↦ hx (h ▸ hgen v)

variable [NoetherianSpace X]

include hdim hgen in
/-- Every `v ∈ V` lies in `V_x` for all but finitely many points `x`. -/
lemma finite_setOf_not_mem_stalkLattice (v : V) :
    {x : X | v ∉ stalkLattice k φ x}.Finite := by
  obtain ⟨U, hU, h⟩ := exists_isOpen_forall_mem_stalkLattice k φ hgen v
  exact (U.isOpen.finite_compl_of_topologicalKrullDim_le_one hdim ⟨_, hU⟩).subset
    fun x hx hxU ↦ hx (h x hxU)

include hdim hgen in
lemma finite_setOf_quotient_mk_ne_zero (v : V) :
    {x : closedPoints X | (Submodule.Quotient.mk v : V ⧸ stalkLattice k φ x.1) ≠ 0}.Finite := by
  refine ((finite_setOf_not_mem_stalkLattice k φ hdim hgen v).preimage
    Subtype.val_injective.injOn).subset fun x hx ↦ ?_
  exact fun h ↦ hx ((Submodule.Quotient.mk_eq_zero _).2 h)

/-- The **principal parts** map `V → ⨁_{x closed} V ⧸ V_x`, `v ↦ (v mod V_x)_x`; it is well
defined since `v ∈ V_x` for all but finitely many `x`. -/
noncomputable def principalPartsMap :
    V →ₗ[k] Π₀ x : closedPoints X, V ⧸ stalkLattice k φ x.1 where
  toFun v := DFinsupp.mkOfFiniteSupport (fun _ ↦ Submodule.Quotient.mk v)
    (finite_setOf_quotient_mk_ne_zero k φ hdim hgen v)
  map_add' _ _ := DFinsupp.ext fun _ ↦ Submodule.Quotient.mk_add _
  map_smul' _ _ := DFinsupp.ext fun _ ↦ Submodule.Quotient.mk_smul _ _ _

@[simp]
lemma principalPartsMap_apply (v : V) (x : closedPoints X) :
    principalPartsMap k φ hdim hgen v x = Submodule.Quotient.mk v :=
  rfl

include hdim hgen in
/-- The components of a global principal part vanish at all but finitely many closed points. -/
lemma finite_setOf_val_ne_zero (s : PrincipalParts k φ ⊤) :
    {x : closedPoints X | s.val φ ⟨x.1, trivial⟩ ≠ 0}.Finite := by
  have h (x : X) := s.property φ ⟨x, trivial⟩
  choose W _hW hxW w hw using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (W x : Set X))
    (fun x ↦ (W x).isOpen) fun y _ ↦ Set.mem_iUnion.2 ⟨y, hxW y⟩
  refine ((Set.Finite.biUnion t.finite_toSet fun x _ ↦
    finite_setOf_not_mem_stalkLattice k φ hdim hgen (w x)).preimage
      Subtype.val_injective.injOn).subset fun y hy ↦ ?_
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y.1))
  refine Set.mem_iUnion₂.2 ⟨x, hx, fun h ↦ hy ?_⟩
  rw [hw x ⟨y.1, trivial⟩ hyx]
  exact (Submodule.Quotient.mk_eq_zero _).2 h

/-- The components at the closed points of a global principal part. -/
noncomputable def globalPrincipalParts :
    Γ(principalParts k φ, ⊤) →+ Π₀ x : closedPoints X, V ⧸ stalkLattice k φ x.1 where
  toFun s := DFinsupp.mkOfFiniteSupport
    (fun x ↦ PrincipalParts.val φ (show PrincipalParts k φ ⊤ from s) ⟨x.1, trivial⟩)
    (finite_setOf_val_ne_zero k φ hdim hgen s)
  map_zero' := DFinsupp.ext fun _ ↦ rfl
  map_add' _ _ := DFinsupp.ext fun _ ↦ rfl

@[simp]
lemma globalPrincipalParts_apply (s : Γ(principalParts k φ, ⊤)) (x : closedPoints X) :
    globalPrincipalParts k φ hdim hgen s x =
      PrincipalParts.val φ (show PrincipalParts k φ ⊤ from s) ⟨x.1, trivial⟩ :=
  rfl

lemma bijective_globalPrincipalParts : Function.Bijective (globalPrincipalParts k φ hdim hgen) := by
  classical
  have := subsingleton_quotient_stalkLattice_genericPoint k φ hgen
  refine ⟨(injective_iff_map_eq_zero _).2 fun s hs ↦ ?_, fun d ↦ ?_⟩
  · refine PrincipalParts.ext φ fun y ↦ ?_
    by_cases hy : y.1 = genericPoint X
    · obtain ⟨y, hy'⟩ := y
      subst hy
      exact Subsingleton.elim _ _
    · exact DFunLike.congr_fun hs ⟨y.1, isClosed_singleton_of_ne_genericPoint hdim hy⟩
  · -- the support of `d`, as a closed subset of `X`
    let S : Set X := Subtype.val '' (d.support : Set (closedPoints X))
    have hSf : S.Finite := (d.support.finite_toSet).image _
    have hScl (T : Set X) (hT : T ⊆ S ∪ {x | ∃ v, v ∉ stalkLattice k φ x ∧ IsClosed {x}})
        (hTf : T.Finite) : IsClosed T :=
      Set.biUnion_of_singleton T ▸ Set.Finite.isClosed_biUnion hTf fun x hx ↦ by
        rcases hT hx with ⟨y, -, rfl⟩ | ⟨-, -, h⟩
        · exact y.2
        · exact h
    let s : (y : (⊤ : X.Opens)) → V ⧸ stalkLattice k φ y.1 := fun y ↦
      if hy : IsClosed {y.1} then d ⟨y.1, hy⟩ else 0
    have hs (y : X) (hy : y ∉ S) : s ⟨y, trivial⟩ = 0 := by
      simp only [s]
      split_ifs with h
      · exact DFinsupp.notMem_support_iff.1 fun h' ↦ hy ⟨⟨y, h⟩, h', rfl⟩
      · rfl
    refine ⟨PrincipalParts.mk φ s fun x ↦ ?_, DFinsupp.ext fun x ↦ ?_⟩
    · obtain ⟨x, -⟩ := x
      by_cases hxS : x ∈ S
      · obtain ⟨x', -, rfl⟩ := hxS
        obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (d x')
        let T : Set X := (S ∪ {y | v ∉ stalkLattice k φ y}) \ {x'.1}
        have hT : IsClosed T :=
          hScl T (fun y hy ↦ hy.1.elim Or.inl fun h ↦ Or.inr
            ⟨v, h, isClosed_singleton_of_not_mem_stalkLattice k φ hdim hgen h⟩)
            ((hSf.union (finite_setOf_not_mem_stalkLattice k φ hdim hgen v)).subset
              Set.sdiff_subset)
        refine ⟨⟨Tᶜ, hT.isOpen_compl⟩, le_top, fun h ↦ h.2 rfl, v, fun ⟨y, _⟩ hy ↦ ?_⟩
        by_cases hyx : y = x'.1
        · subst hyx
          exact (dite_eq_left (show IsClosed {x'.1} from x'.2)).trans hv.symm
        · have hyS : y ∉ S := fun h ↦ hy ⟨Or.inl h, hyx⟩
          have hyv : v ∈ stalkLattice k φ y := by
            by_contra h
            exact hy ⟨Or.inr h, hyx⟩
          rw [hs y hyS]
          exact ((Submodule.Quotient.mk_eq_zero _).2 hyv).symm
      · have hScl' : IsClosed S := hScl S Set.subset_union_left hSf
        refine ⟨⟨Sᶜ, hScl'.isOpen_compl⟩, le_top, hxS, 0, fun y hy ↦ ?_⟩
        rw [hs y.1 hy, Submodule.Quotient.mk_zero]
    · exact dite_eq_left x.2

/-- The global principal parts are the finitely supported families of classes at the closed
points. -/
noncomputable def globalPrincipalPartsEquiv :
    Γ(principalParts k φ, ⊤) ≃+ Π₀ x : closedPoints X, V ⧸ stalkLattice k φ x.1 :=
  AddEquiv.ofBijective (globalPrincipalParts k φ hdim hgen)
    (bijective_globalPrincipalParts k φ hdim hgen)

lemma globalPrincipalParts_toPrincipalPartsTop (t : Γ(skyscraper (genericPoint X) V, ⊤)) :
    globalPrincipalParts k φ hdim hgen (toPrincipalPartsTop k φ t) =
      principalPartsMap k φ hdim hgen
        ((show SkyscraperSections (genericPoint X) V ⊤ from t) ⟨trivial⟩) :=
  DFinsupp.ext fun _ ↦ rfl

lemma globalPrincipalParts_smul (c : k) (s : Γ(principalParts k φ, ⊤)) :
    globalPrincipalParts k φ hdim hgen (globalSectionsRingHom k (X := X) c • s) =
      c • globalPrincipalParts k φ hdim hgen s := by
  refine DFinsupp.ext fun x ↦ ?_
  change quotSMul φ (U := ⊤) trivial _ (PrincipalParts.val φ (show PrincipalParts k φ ⊤ from s) _) =
    c • PrincipalParts.val φ (show PrincipalParts k φ ⊤ from s) _
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _
    (PrincipalParts.val φ (show PrincipalParts k φ ⊤ from s) ⟨x.1, trivial⟩)
  rw [← hv, quotSMul_mk, ← Submodule.Quotient.mk_smul]
  congr 1
  rw [← algebraMap_smul X.functionField c v, IsFunctionFieldAlgebra.algebraMap_eq]

end Finiteness

section H1

variable [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1)
  (hgen : ∀ v : V, v ∈ stalkLattice k φ (genericPoint X))
  {φ} (hφ : ∀ U, Function.Injective (φ.app U))

/-- The surjection `⨁_x V ⧸ V_x ⟶ H¹(X, M)` given by the connecting map of the residue sequence.
-/
noncomputable def adelicToH1 :
    (Π₀ x : closedPoints X, V ⧸ stalkLattice k φ x.1) →ₗ[k] M.H 1 where
  toFun d := residueδ k hφ ((globalPrincipalPartsEquiv k φ hdim hgen).symm d)
  map_add' _ _ := by rw [map_add, map_add]
  map_smul' c d := by
    have : (globalPrincipalPartsEquiv k φ hdim hgen).symm (c • d) =
        globalSectionsRingHom k (X := X) c • (globalPrincipalPartsEquiv k φ hdim hgen).symm d := by
      apply (globalPrincipalPartsEquiv k φ hdim hgen).injective
      rw [AddEquiv.apply_symm_apply]
      change _ = globalPrincipalParts k φ hdim hgen _
      rw [globalPrincipalParts_smul]
      exact (congrArg _ ((globalPrincipalPartsEquiv k φ hdim hgen).apply_symm_apply d)).symm
    rw [this, LinearMap.map_smul]
    rfl

lemma adelicToH1_apply (d : Π₀ x : closedPoints X, V ⧸ stalkLattice k φ x.1) :
    adelicToH1 k hdim hgen hφ d =
      residueδ k hφ ((globalPrincipalPartsEquiv k φ hdim hgen).symm d) :=
  rfl

lemma surjective_adelicToH1 : Function.Surjective (adelicToH1 k hdim hgen hφ) :=
  (surjective_residueδ k hφ).comp (globalPrincipalPartsEquiv k φ hdim hgen).symm.surjective

lemma ker_adelicToH1 :
    LinearMap.ker (adelicToH1 k hdim hgen hφ) =
      LinearMap.range (principalPartsMap k φ hdim hgen) := by
  ext d
  rw [LinearMap.mem_ker, adelicToH1_apply, ← LinearMap.mem_ker, ker_residueδ]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨(show SkyscraperSections (genericPoint X) V ⊤ from t) ⟨trivial⟩, ?_⟩
    rw [← globalPrincipalParts_toPrincipalPartsTop, ht]
    exact (globalPrincipalPartsEquiv k φ hdim hgen).apply_symm_apply d
  · rintro ⟨v, rfl⟩
    refine ⟨show SkyscraperSections (genericPoint X) V ⊤ from fun _ ↦ v, ?_⟩
    apply (globalPrincipalPartsEquiv k φ hdim hgen).injective
    rw [AddEquiv.apply_symm_apply]
    exact globalPrincipalParts_toPrincipalPartsTop k φ hdim hgen _

/-- **`H¹` of a module on a curve via principal parts.** Let `X` be an integral noetherian
scheme of dimension at most one over `k`, and `φ : M ⟶ V_η` injective on sections with every
`v ∈ V` the value of a local section. Then the connecting map of the residue sequence induces a
canonical `k`-linear isomorphism
`H¹(X, M) ≅ (⨁_{x closed} V ⧸ V_x) ⧸ V`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
noncomputable def adelicH1Equiv :
    M.H 1 ≃ₗ[k] (Π₀ x : closedPoints X, V ⧸ stalkLattice k φ x.1) ⧸
      LinearMap.range (principalPartsMap k φ hdim hgen) :=
  (((LinearMap.range (principalPartsMap k φ hdim hgen)).quotEquivOfEq _
    (ker_adelicToH1 k hdim hgen hφ).symm).trans
    ((adelicToH1 k hdim hgen hφ).quotKerEquivOfSurjective
      (surjective_adelicToH1 k hdim hgen hφ))).symm

lemma adelicH1Equiv_symm_mk (d : Π₀ x : closedPoints X, V ⧸ stalkLattice k φ x.1) :
    (adelicH1Equiv k hdim hgen hφ).symm (Submodule.Quotient.mk d) =
      adelicToH1 k hdim hgen hφ d :=
  rfl

variable (φ) in
omit [NoetherianSpace X] in
/-- The value in `V` of a global section of `M`, as a `k`-linear map on `H⁰(X, M)`. -/
noncomputable def adelicH0Map : M.H 0 →ₗ[k] ↥(⨅ x : closedPoints X, stalkLattice k φ x.1) where
  toFun z := ⟨genericValue φ (U := ⊤) trivial (H.zeroLinearEquiv M z),
    (Submodule.mem_iInf _).2 fun x ↦
      genericValue_mem_stalkLattice φ (U := ⊤) (x := x.1) trivial _⟩
  map_add' z z' := by
    refine Subtype.ext ?_
    change genericValue φ (U := ⊤) trivial (H.zeroLinearEquiv M (z + z')) =
      genericValue φ (U := ⊤) trivial (H.zeroLinearEquiv M z) +
        genericValue φ (U := ⊤) trivial (H.zeroLinearEquiv M z')
    rw [map_add, genericValue_add]
  map_smul' c z := by
    refine Subtype.ext ?_
    change genericValue φ (U := ⊤) trivial
        (H.zeroLinearEquiv M (globalSectionsRingHom k (X := X) c • z)) =
      c • genericValue φ (U := ⊤) trivial (H.zeroLinearEquiv M z)
    rw [LinearEquiv.map_smul, genericValue_smul, ← IsFunctionFieldAlgebra.algebraMap_eq,
      algebraMap_smul]

variable (φ) in
omit [NoetherianSpace X] in
lemma adelicH0Map_apply (z : M.H 0) :
    (adelicH0Map k φ z : V) = genericValue φ (U := ⊤) trivial (H.zeroLinearEquiv M z) :=
  rfl

omit [NoetherianSpace X] in
include hdim hgen hφ in
lemma bijective_adelicH0Map : Function.Bijective (adelicH0Map k φ) := by
  refine ⟨fun z z' h ↦ (H.zeroLinearEquiv M).injective (hφ ⊤ ?_), fun w ↦ ?_⟩
  · exact SkyscraperSections.ext fun _ ↦ congr_arg Subtype.val h
  · have hw (y : X) (_ : y ∈ (⊤ : X.Opens)) : w.1 ∈ stalkLattice k φ y := by
      by_cases hyη : y = genericPoint X
      · exact hyη ▸ hgen w.1
      · exact (Submodule.mem_iInf _).1 w.2 ⟨y, isClosed_singleton_of_ne_genericPoint hdim hyη⟩
    obtain ⟨s, hs⟩ := exists_app_eq_of_forall_mem hφ
      (show SkyscraperSections (genericPoint X) V ⊤ from fun _ ↦ w.1) hw
    refine ⟨(H.zeroLinearEquiv M).symm s, Subtype.ext ?_⟩
    rw [adelicH0Map_apply, LinearEquiv.apply_symm_apply]
    exact congr_arg (fun t : SkyscraperSections (genericPoint X) V ⊤ ↦ t ⟨trivial⟩) hs

omit [NoetherianSpace X] in
/-- **`H⁰` of a module on a curve.** Under the hypotheses of
`AlgebraicGeometry.Scheme.Modules.adelicH1Equiv`, taking values in `V` identifies
`H⁰(X, M) = Γ(X, M)` with `⋂_{x closed} V_x`. -/
noncomputable def adelicH0Equiv :
    M.H 0 ≃ₗ[k] ↥(⨅ x : closedPoints X, stalkLattice k φ x.1) :=
  LinearEquiv.ofBijective (adelicH0Map k φ) (bijective_adelicH0Map k hdim hgen hφ)

omit [NoetherianSpace X] in
lemma adelicH0Equiv_apply (z : M.H 0) :
    (adelicH0Equiv k hdim hgen hφ z : V) =
      genericValue φ (U := ⊤) trivial (H.zeroLinearEquiv M z) :=
  rfl

end H1

end Modules

end AlgebraicGeometry.Scheme
