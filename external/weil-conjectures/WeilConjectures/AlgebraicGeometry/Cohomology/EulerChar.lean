/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import WeilConjectures.AlgebraicGeometry.Cohomology.Clopen
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Vanishing
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.ZariskiDimensionBound
import Mathlib.Topology.Sheaves.Abelian
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologySeparated
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyGluing
import WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The arithmetic genus and the cohomological degree of a sheaf of modules

Let `X` be a scheme over a field `k`. We define its arithmetic genus `dim_k H^1(X, 𝒪_X)` and the
degree `deg ℒ = χ(ℒ) - χ(𝒪_X)` of an invertible sheaf on it, both in terms of the cohomological
invariants `AlgebraicGeometry.Scheme.Modules.finrankH` and the Euler characteristic
`AlgebraicGeometry.Scheme.Modules.eulerChar`.

There is no group of Cartier or Weil divisors on a scheme in Mathlib. The degree is therefore
*defined* cohomologically, which is the standard alternative definition (Stacks 0AYQ). On a
smooth proper curve it agrees with the degree `dim_k Γ(D, 𝒪_D)` of divisors; this is part of
Riemann–Roch, stated in `WeilConjectures/AlgebraicGeometry/Curve/RiemannRoch.lean`.

## Main definitions

- `AlgebraicGeometry.Scheme.arithmeticGenus`: the arithmetic genus `dim_k H^1(X, 𝒪_X)`.
- `AlgebraicGeometry.Scheme.Modules.degree`: the degree `χ(ℒ) - χ(𝒪_X)` of an invertible sheaf.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt`: Grothendieck
  vanishing, which makes the `finsum` defining the Euler characteristic a finite sum on a
  noetherian scheme of finite dimension.
- `AlgebraicGeometry.Scheme.Modules.nonempty_H_pullback_linearEquiv`: flat base change of
  cohomology along a field extension, `H^q(X_K, M_K) ≅ H^q(X, M) ⊗_k K`.
- `AlgebraicGeometry.Scheme.arithmeticGenus_pullback`,
  `AlgebraicGeometry.Scheme.Modules.degree_pullback`: the arithmetic genus and the degree are
  invariant under base change along a field extension.
- `AlgebraicGeometry.Scheme.Modules.degree_congr`: the degree only depends on the isomorphism
  class of the sheaf.
- `AlgebraicGeometry.Scheme.Modules.degree_unit`: the structure sheaf has degree `0`.
- `AlgebraicGeometry.Scheme.Modules.finrankH_eq_sum_of_pairwise_disjoint`: the cohomology of a
  finite disjoint union of open subschemes is the direct sum of the cohomologies of the pieces.
- `AlgebraicGeometry.Scheme.Modules.eulerChar_eq_sum_of_pairwise_disjoint`: the Euler
  characteristic is additive over a finite disjoint union of open subschemes.
-/

@[expose] public section

universe u

open CategoryTheory Function TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- **Grothendieck vanishing.** On a noetherian scheme `X` of dimension `n`, the cohomology of
every sheaf of modules vanishes in degrees `q > n`.

This is what makes the `finsum` defining `AlgebraicGeometry.Scheme.Modules.eulerChar` a finite
sum, hence makes `χ`, the genus and the degree meaningful, for instance on a curve, where
`n = 1`. 
(blueprint: lem-sc-noetherian-cohomology-above-dimension)
-/
@[stacks 02UZ]
theorem Modules.subsingleton_H_of_topologicalKrullDim_lt {X : Scheme.{u}} [IsNoetherian X]
    (ℱ : X.Modules) {q : ℕ} (hq : topologicalKrullDim X < q) : Subsingleton (ℱ.H q) := by
  classical
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ
  by_cases hX : Nonempty X
  · obtain ⟨x⟩ := hX
    have : Nonempty (IrreducibleCloseds X) :=
      ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have hnonneg : 0 ≤ topologicalKrullDim X := Order.krullDim_nonneg
    cases q with
    | zero => exact False.elim (not_lt_of_ge hnonneg hq)
    | succ n =>
      have hdim : topologicalKrullDim X ≤ (n : WithBot ℕ∞) := by
        apply ENat.WithBot.lt_add_one_iff.mp
        simpa only [Nat.cast_add, Nat.cast_one] using hq
      have hz := AlgebraicGeometry.isZero_zariskiCohomology_of_dimension_bound
        X n hdim F (n + 1) n.lt_succ_self
      let e : (yoneda.obj (⊤ : X.Opens) ⋙ AddCommGrpCat.free) ≅
          (Functor.const X.Opensᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ)) :=
        NatIso.ofComponents (fun U ↦ by
          letI : Unique (U.unop ⟶ (⊤ : X.Opens)) :=
            ⟨⟨homOfLE le_top⟩, fun f ↦ Subsingleton.elim f _⟩
          exact ((FreeAbelianGroup.uniqueEquiv _).trans AddEquiv.ulift.symm).toAddCommGrpIso)
          (by
            intro U V f
            ext g
            change ULift.up ((FreeAbelianGroup.lift fun _ ↦ (1 : ℤ))
                (FreeAbelianGroup.map (fun g ↦ f.unop ≫ g) g)) =
              ULift.up ((FreeAbelianGroup.lift fun _ ↦ (1 : ℤ)) g)
            rw [← FreeAbelianGroup.lift_comp]
            rfl)
      let e' := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso e
      have : Subsingleton (F.H' (n + 1) ⊤) := AddCommGrpCat.subsingleton_of_isZero hz
      let a : ℱ.H (n + 1) ≃+ (F.H' (n + 1) ⊤) :=
        Abelian.Ext.precompAddEquiv e' F (n + 1)
      exact a.injective.subsingleton
  · have : IsEmpty X := not_nonempty_iff.mp hX
    have hz : Limits.IsZero F :=
      (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero F).mpr fun x ↦ isEmptyElim x
    exact Sheaf.subsingleton_H_of_isZero hz q

section Defs

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The **arithmetic genus** `dim_k H^1(X, 𝒪_X)` of a `k`-scheme `X`.

When `X` is a smooth proper curve over `k` with `H⁰(X, 𝒪_X) = k`
(`AlgebraicGeometry.Scheme.GlobalSectionsBijective`) this is the genus of `X`; no hypotheses
are imposed on `X` here, so for other `X` the value carries no meaning.

For a smooth proper curve `X ↘ Spec k`, Serre duality identifies this with
`AlgebraicGeometry.Scheme.Hom.genus (X ↘ Spec k) = dim_k H^0(X, Ω¹_{X/k})`; see
`AlgebraicGeometry.Scheme.genus_eq_arithmeticGenus`.

(blueprint: `def-pc-genus`) 
(blueprint: def-pc-genus)
-/
noncomputable def arithmeticGenus : ℕ :=
  Modules.finrankH (X := X) k (SheafOfModules.unit X.ringCatSheaf) 1

end Defs

section BaseChange

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  (K : Type u) [Field K] [Algebra k K]

/-- **Flat base change of cohomology along a field extension.** Let `X` be a quasi-compact
quasi-separated scheme over a field `k`, let `K/k` be a field extension and let `M` be a
quasi-coherent `𝒪_X`-module. Then `H^q(X_K, M_K) ≅ H^q(X, M) ⊗_k K` as `K`-vector spaces, where
`X_K = X ×_{Spec k} Spec K` and `M_K` is the pullback of `M` to `X_K`.

Proof (Stacks 02KH): first suppose `X` is separated. A finite affine open cover has affine
intersections, so its Čech complex computes quasi-coherent cohomology. The affine pullback
section formula identifies the base-changed complex with its tensor product by `K`.
Tensoring over the field `k` is exact, hence commutes with cohomology. For general
quasi-separated `X`, use compact-open induction. Its step adds an affine open `V` to a
compact open `U`. The overlap `U ∩ V` is compact by quasi-separatedness and separated
because it is open in the affine scheme `V`; it need not be affine. The separated case
applies to `V` and the overlap, while the induction hypothesis applies to `U`.
Mayer--Vietoris gluing of the canonical comparisons proves bijectivity on `U ∪ V` in
all degrees. Apply the induction at the whole scheme and invert the resulting
`K`-linear comparison from `K ⊗[k] H^q(X, M)` to the pullback cohomology.

(blueprint: `lem-pc-flat-base-change-cohom`) 
(blueprint: lem-pc-flat-base-change-cohom)
-/
@[stacks 02KH]
theorem Modules.nonempty_H_pullback_linearEquiv [QuasiCompact (X ↘ Spec (.of k))]
    [QuasiSeparated (X ↘ Spec (.of k))] (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Nonempty (((Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M).H q ≃ₗ[K]
        TensorProduct k K (M.H q)) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  let P (U : X.Opens) : Prop :=
    ∀ (Y : Scheme.{u}) (j : Y ⟶ X) (_ : IsOpenImmersion j), j.opensRange = U →
      ∀ (N : Y.Modules) (_ : N.IsQuasicoherent) (n : ℕ),
        Function.Bijective (Modules.H.baseChange (S := K) (j ≫ X ↘ Spec (.of k)) N n)
  have hP : P ⊤ := by
    apply compact_open_induction_on (P := P) ⊤ isCompact_univ
    · intro Y j hj hjrange N hN n
      have : IsEmpty Y := ⟨fun y ↦ by
        have hy : j y ∈ j.opensRange := ⟨y, rfl⟩
        rw [hjrange] at hy
        exact hy⟩
      exact Modules.H.baseChange_bijective_of_isSeparated _ N n
    · intro U hU V ih Y j hj hjrange N hN n
      let A : Y.Opens := j ⁻¹ᵁ U
      let B : Y.Opens := j ⁻¹ᵁ V.1
      have hAimage : j ''ᵁ A = U := by
        rw [Hom.image_preimage_eq_opensRange_inf, hjrange, inf_eq_right.mpr le_sup_left]
      have hB : IsAffineOpen B :=
        V.2.preimage_of_isOpenImmersion j (hjrange.symm ▸ le_sup_right)
      have hAc : IsCompact (A : Set Y) :=
        j.isOpenEmbedding.isEmbedding.isCompact_iff.mpr (by
          change IsCompact (j ''ᵁ A : Set X)
          rw [hAimage]
          exact hU)
      have : CompactSpace A.toScheme := isCompact_iff_compactSpace.mp hAc
      have : QuasiSeparatedSpace Y := j.isOpenEmbedding.quasiSeparatedSpace
      have hIc : IsCompact ((A ⊓ B : Y.Opens) : Set Y) :=
        hAc.inter_of_isOpen hB.isCompact A.isOpen B.isOpen
      have : CompactSpace (A ⊓ B).toScheme := isCompact_iff_compactSpace.mp hIc
      have : IsAffine B.toScheme := hB
      have : (A ⊓ B).toScheme.IsSeparated := ⟨by
        rw [← Limits.terminal.comp_from (Y.homOfLE (inf_le_right : A ⊓ B ≤ B))]
        infer_instance⟩
      apply Modules.H.baseChange_bijective_of_openCover _ N A B ?_ ?_ ?_ ?_ n
      · change j ⁻¹ᵁ U ⊔ j ⁻¹ᵁ V.1 = ⊤
        rw [← j.preimage_sup, ← hjrange, j.preimage_opensRange]
      · intro r
        apply ih A.toScheme (A.ι ≫ j) inferInstance ?_ _ inferInstance r
        rw [Hom.opensRange_comp, Opens.opensRange_ι, hAimage]
      · intro r
        exact Modules.H.baseChange_bijective_of_isSeparated _ _ r
      · intro r
        exact Modules.H.baseChange_bijective_of_isSeparated _ _ r
  have hb := hP X (𝟙 X) inferInstance (Hom.opensRange_of_isIso _) M inferInstance q
  exact ⟨(LinearEquiv.ofBijective (Modules.H.baseChange (S := K)
    (X ↘ Spec (.of k)) M q) hb).symm⟩

/-- **Flat base change of `h^q`.** For a quasi-coherent module `M` on a quasi-compact
quasi-separated scheme `X` over `k` and a field extension `K/k`,
`dim_K H^q(X_K, M_K) = dim_k H^q(X, M)`.

(blueprint: `lem-pc-flat-base-change-cohom`) 
(blueprint: lem-pc-flat-base-change-cohom)
-/
theorem Modules.finrankH_pullback [QuasiCompact (X ↘ Spec (.of k))]
    [QuasiSeparated (X ↘ Spec (.of k))] (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    ((Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M).finrankH K q =
      M.finrankH k q := by
  obtain ⟨e⟩ := Modules.nonempty_H_pullback_linearEquiv (k := k) K M q
  exact e.finrank_eq.trans Module.finrank_baseChange

/-- **Flat base change of `χ`.** For a quasi-coherent module `M` on a quasi-compact
quasi-separated scheme `X` over `k` and a field extension `K/k`, `χ(X_K, M_K) = χ(X, M)`. -/
theorem Modules.eulerChar_pullback [QuasiCompact (X ↘ Spec (.of k))]
    [QuasiSeparated (X ↘ Spec (.of k))] (M : X.Modules) [M.IsQuasicoherent] :
    ((Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M).eulerChar K =
      M.eulerChar k := by
  simp only [Modules.eulerChar, Modules.finrankH_pullback]

/-- **The genus is invariant under base change.** Let `X` be a quasi-compact quasi-separated
scheme over a field `k` and let `K/k` be a field extension. Then the base change
`X_K = X ×_{Spec k} Spec K` has `dim_K H¹(X_K, 𝒪_{X_K}) = dim_k H¹(X, 𝒪_X)`: by flat base change
`H¹(X_K, 𝒪_{X_K}) ≅ H¹(X, 𝒪_X) ⊗_k K` (Stacks 02KH).

(blueprint: `corollary-serre-duality-field-extension--2`) 
(blueprint: corollary-serre-duality-field-extension--2)
-/
theorem arithmeticGenus_pullback [QuasiCompact (X ↘ Spec (.of k))]
    [QuasiSeparated (X ↘ Spec (.of k))] :
    arithmeticGenus K
        (Limits.pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))) =
      arithmeticGenus k X :=
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  (Modules.finrankH_congr K (Modules.pullbackObjUnitIso _).symm 1).trans
    (Modules.finrankH_pullback K (SheafOfModules.unit X.ringCatSheaf) 1)

end BaseChange

section Degree

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The **degree** `deg ℒ = χ(ℒ) - χ(𝒪_X)` of a sheaf of modules `ℒ` on a `k`-scheme `X`
(Stacks 0AYQ).

The value is the degree in the usual sense only for an invertible `ℒ` on a proper curve, where
it agrees with the degree of the associated divisor class; for other sheaves it is just a
difference of Euler characteristics.

(blueprint: `def-pc-degree-line-bundle`) 
(blueprint: def-pc-degree-line-bundle)
-/
noncomputable def Modules.degree (M : X.Modules) : ℤ :=
  M.eulerChar k - Modules.eulerChar (X := X) k (SheafOfModules.unit X.ringCatSheaf)

/-- The degree only depends on the isomorphism class of a sheaf of modules. -/
lemma Modules.degree_congr {M N : X.Modules} (e : M ≅ N) : M.degree k = N.degree k := by
  rw [degree, degree, eulerChar_congr k e]

@[simp]
lemma Modules.degree_unit :
    Modules.degree (X := X) k (SheafOfModules.unit X.ringCatSheaf) = 0 :=
  sub_self _

/-- **The degree is invariant under base change** (blueprint
`theorem-riemann-roch-coherent-serre-duality--1`, part (1)). For a quasi-coherent module `M` on a
quasi-compact quasi-separated scheme `X` over `k` and a field extension `K/k`,
`deg_{X_K}(M_K) = deg_X(M)`: both Euler characteristics in `deg M = χ(M) - χ(𝒪_X)` are invariant
under flat base change.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--1`) 
(blueprint: theorem-riemann-roch-coherent-serre-duality--1)
-/
theorem Modules.degree_pullback (K : Type u) [Field K] [Algebra k K]
    [QuasiCompact (X ↘ Spec (.of k))] [QuasiSeparated (X ↘ Spec (.of k))] (M : X.Modules)
    [M.IsQuasicoherent] :
    ((Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M).degree K = M.degree k := by
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  rw [Modules.degree, Modules.degree, Modules.eulerChar_pullback]
  congr 1
  exact (Modules.eulerChar_congr K (Modules.pullbackObjUnitIso _).symm).trans
    (Modules.eulerChar_pullback K _)

end Degree

namespace Modules

section Additivity

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

open Limits in
attribute [local instance] Abelian.hasFiniteBiproducts in
/-- `AlgebraicGeometry.Scheme.Modules.finrankH_eq_sum_of_pairwise_disjoint` for an index type in
`Type`. -/
private theorem finrankH_eq_sum_of_pairwise_disjoint_aux {ι : Type} [Fintype ι]
    (U : ι → X.Opens) (hU : _root_.Pairwise (Disjoint on U)) (hcover : ⨆ i, U i = ⊤)
    (M : X.Modules) (q : ℕ) [FiniteDimensional k (M.H q)] :
    M.finrankH k q = ∑ i,
      letI : (U i).toScheme.Over (Spec (.of k)) := ⟨(U i).ι ≫ X ↘ Spec (.of k)⟩
      ((Scheme.Modules.pullback (U i).ι).obj M).finrankH k q := by
  classical
  -- Each `U i` is closed, its complement being the union of the other `U j`.
  have hclosed (i : ι) : IsClosed (U i : Set X) := by
    have : (U i : Set X)ᶜ = (⨆ j : {j // j ≠ i}, U j : X.Opens) := by
      ext x
      simp only [Opens.coe_iSup, Set.mem_iUnion, Set.mem_compl_iff, SetLike.mem_coe]
      refine ⟨fun hi ↦ ?_, fun ⟨j, hj⟩ hi ↦ (Opens.coe_disjoint.mpr (hU j.2)).le_bot ⟨hj, hi⟩⟩
      have hx : x ∈ ⨆ i, U i := by rw [hcover]; trivial
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
      exact ⟨⟨j, fun h ↦ hi (h ▸ hj)⟩, hj⟩
    rw [← isOpen_compl_iff, this]
    exact Opens.isOpen _
  let N (i : ι) : X.Modules := (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj M
  let φ : M ≅ ⨁ N := @asIso _ _ _ _ (biproduct.lift fun i ↦
    (restrictAdjunction (U i).ι).unit.app M)
    (isIso_biproduct_lift_restrictAdjunction_unit U hU hcover M)
  let e := H.isBilimitLinearEquiv k (biproduct.isBilimit N) q
  have hφ : Function.Surjective (H.mapLinearMap k φ.hom q) := fun y ↦
    ⟨H.map φ.inv q y, by rw [H.mapLinearMap_apply, ← H.map_comp_apply, φ.inv_hom_id,
      H.map_id_apply]⟩
  have := Module.Finite.of_surjective (e.toLinearMap ∘ₗ H.mapLinearMap k φ.hom q)
    (e.surjective.comp hφ)
  have (i : ι) := Module.Finite.of_surjective (LinearMap.proj (R := k) i)
    (LinearMap.proj_surjective (φ := fun i ↦ (N i).H q) i)
  rw [finrankH_congr k φ q, finrankH_of_isBilimit k (biproduct.isBilimit N) q]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  let : (U i).toScheme.Over (Spec (.of k)) := ⟨(U i).ι ≫ X ↘ Spec (.of k)⟩
  exact (finrankH_pushforward_ι (U i) (hclosed i) k _ q).trans
    (finrankH_congr k ((restrictFunctorIsoPullback (U i).ι).app M) q)

/-- **Cohomology of a finite disjoint union.** If `X` is the disjoint union of finitely many
open subschemes `U i`, then `H^q(X, M) ≅ ⊕ᵢ H^q(U i, M|_{U i})`; in particular, when
`H^q(X, M)` is finite-dimensional, `h^q(X, M) = ∑ᵢ h^q(U i, M|_{U i})`. Each `U i` is a scheme
over `k` through `X`.

Each `U i` is open and closed, `M` is the direct sum of the pushforwards of its restrictions to
the `U i` (`AlgebraicGeometry.Scheme.Modules.isIso_biproduct_lift_restrictAdjunction_unit`), and
the pushforward along the inclusion of an open and closed subscheme does not change cohomology
(`AlgebraicGeometry.Scheme.Modules.finrankH_pushforward_ι`).

This is used in the proof of blueprint `proposition-multiplication-n--1`. -/
theorem finrankH_eq_sum_of_pairwise_disjoint {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (hU : _root_.Pairwise (Disjoint on U)) (hcover : ⨆ i, U i = ⊤) (M : X.Modules) (q : ℕ)
    [FiniteDimensional k (M.H q)] :
    M.finrankH k q = ∑ i,
      letI : (U i).toScheme.Over (Spec (.of k)) := ⟨(U i).ι ≫ X ↘ Spec (.of k)⟩
      ((Scheme.Modules.pullback (U i).ι).obj M).finrankH k q := by
  let e := Fintype.equivFin ι
  rw [← e.symm.sum_comp]
  refine finrankH_eq_sum_of_pairwise_disjoint_aux k (U ∘ e.symm)
    (hU.comp_of_injective e.symm.injective) ?_ M q
  rw [← hcover]
  exact (e.symm.surjective.iSup_comp U)

/-- On a noetherian scheme, `h^q(X, M) = 0` above the dimension of `X`, by Grothendieck
vanishing. -/
theorem finrankH_eq_zero_of_topologicalKrullDim_lt [IsNoetherian X] (M : X.Modules) {q : ℕ}
    (hq : topologicalKrullDim X < q) : M.finrankH k q = 0 :=
  have := subsingleton_H_of_topologicalKrullDim_lt M hq
  Module.finrank_zero_of_subsingleton

/-- On a noetherian scheme of dimension at most `n`, the Euler characteristic is the finite sum
`∑_{q ≤ n} (-1)^q h^q(X, M)`. -/
theorem eulerChar_eq_sum_range [IsNoetherian X] (M : X.Modules) {n : ℕ}
    (hn : topologicalKrullDim X ≤ n) :
    M.eulerChar k = ∑ q ∈ Finset.range (n + 1), (-1) ^ q * (M.finrankH k q : ℤ) := by
  refine finsum_eq_sum_of_support_subset _ fun q hq ↦ ?_
  by_contra h
  refine hq ?_
  change (-1) ^ q * (M.finrankH k q : ℤ) = 0
  rw [finrankH_eq_zero_of_topologicalKrullDim_lt k M (hn.trans_lt ?_), Nat.cast_zero, mul_zero]
  simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
  exact_mod_cast Nat.lt_of_lt_of_le n.lt_succ_self h

/-- **The Euler characteristic is additive over a finite disjoint union.** If a noetherian
scheme `X` of finite dimension is the disjoint union of finitely many open subschemes `U i`,
and the cohomology of `M` is finite-dimensional, then `χ(X, M) = ∑ᵢ χ(U i, M|_{U i})`. -/
theorem eulerChar_eq_sum_of_pairwise_disjoint [IsNoetherian X] {n : ℕ}
    (hn : topologicalKrullDim X ≤ n) {ι : Type*}
    [Fintype ι] (U : ι → X.Opens) (hU : _root_.Pairwise (Disjoint on U)) (hcover : ⨆ i, U i = ⊤)
    (M : X.Modules) [∀ q, FiniteDimensional k (M.H q)] :
    M.eulerChar k = ∑ i,
      letI : (U i).toScheme.Over (Spec (.of k)) := ⟨(U i).ι ≫ X ↘ Spec (.of k)⟩
      ((Scheme.Modules.pullback (U i).ι).obj M).eulerChar k := by
  let (i : ι) : (U i).toScheme.Over (Spec (.of k)) := ⟨(U i).ι ≫ X ↘ Spec (.of k)⟩
  have (i : ι) : IsNoetherian (U i) :=
    { toCompactSpace := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _) }
  rw [eulerChar_eq_sum_range k M hn]
  simp_rw [finrankH_eq_sum_of_pairwise_disjoint k U hU hcover M, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eulerChar_eq_sum_range k _ ((topologicalKrullDim_subspace_le X (U i)).trans hn)]

/-- If `H^q(X, M) = 0` for `q > D`, the Euler characteristic of `M` is the finite sum
`∑_{q ≤ D} (-1)^q h^q(X, M)`. -/
theorem eulerChar_eq_sum_range_of_subsingleton (M : X.Modules) {D : ℕ}
    (hD : ∀ q, D < q → Subsingleton (M.H q)) :
    M.eulerChar k = ∑ q ∈ Finset.range (D + 1), (-1) ^ q * (M.finrankH k q : ℤ) := by
  refine finsum_eq_sum_of_support_subset _ fun q hq ↦ ?_
  by_contra h
  refine hq ?_
  change (-1) ^ q * (M.finrankH k q : ℤ) = 0
  simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
  have := hD q (by omega)
  rw [finrankH, Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]

/-- **The Euler characteristic of a quasi-coherent module is additive over a finite disjoint
union.** If a quasi-compact separated scheme `X` is the disjoint union of finitely many open
subschemes `U i`, and the cohomology of the quasi-coherent module `M` is finite-dimensional, then
`χ(X, M) = ∑ᵢ χ(U i, M|_{U i})`.

This is `AlgebraicGeometry.Scheme.Modules.eulerChar_eq_sum_of_pairwise_disjoint` without the
appeal to Grothendieck vanishing: the cohomology of quasi-coherent modules on `X` and on the `U i`
vanishes above the number of affine opens needed to cover them
(`AlgebraicGeometry.Scheme.Modules.exists_forall_subsingleton_H_of_isQuasicoherent`). -/
theorem eulerChar_eq_sum_of_pairwise_disjoint_of_isQuasicoherent [CompactSpace X]
    [IsSeparated (Limits.terminal.from X)] {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (hU : _root_.Pairwise (Disjoint on U)) (hcover : ⨆ i, U i = ⊤) (M : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    [∀ q, FiniteDimensional k (M.H q)] :
    M.eulerChar k = ∑ i,
      letI : (U i).toScheme.Over (Spec (.of k)) := ⟨(U i).ι ≫ X ↘ Spec (.of k)⟩
      ((Scheme.Modules.pullback (U i).ι).obj M).eulerChar k := by
  classical
  let (i : ι) : (U i).toScheme.Over (Spec (.of k)) := ⟨(U i).ι ≫ X ↘ Spec (.of k)⟩
  have hclosed (i : ι) : IsClosed (U i : Set X) := by
    have : (U i : Set X)ᶜ = (⨆ j : {j // j ≠ i}, U j : X.Opens) := by
      ext x
      simp only [Opens.coe_iSup, Set.mem_iUnion, Set.mem_compl_iff, SetLike.mem_coe]
      refine ⟨fun hi ↦ ?_, fun ⟨j, hj⟩ hi ↦ (Opens.coe_disjoint.mpr (hU j.2)).le_bot ⟨hj, hi⟩⟩
      have hx : x ∈ ⨆ i, U i := by rw [hcover]; trivial
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
      exact ⟨⟨j, fun h ↦ hi (h ▸ hj)⟩, hj⟩
    rw [← isOpen_compl_iff, this]
    exact Opens.isOpen _
  have (i : ι) : CompactSpace (U i) := isCompact_iff_compactSpace.mp (hclosed i).isCompact
  have (i : ι) : IsSeparated (Limits.terminal.from (U i).toScheme) := by
    rw [← Limits.terminal.comp_from (U i).ι]
    infer_instance
  obtain ⟨D₀, hD₀⟩ := exists_forall_subsingleton_H_of_isQuasicoherent (X := X)
  choose D hD using fun i ↦ exists_forall_subsingleton_H_of_isQuasicoherent (X := U i)
  have hle (i : ι) : D i ≤ D₀ + ∑ j, D j :=
    le_add_left (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (D j)) (Finset.mem_univ i))
  rw [eulerChar_eq_sum_range_of_subsingleton k M (D := D₀ + ∑ j, D j)
    fun q hq ↦ hD₀ M q (by omega)]
  simp_rw [finrankH_eq_sum_of_pairwise_disjoint k U hU hcover M, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eulerChar_eq_sum_range_of_subsingleton k _ (D := D₀ + ∑ j, D j)
    fun q hq ↦ hD i _ q ((hle i).trans_lt hq)]

end Additivity

end Modules

end AlgebraicGeometry.Scheme

