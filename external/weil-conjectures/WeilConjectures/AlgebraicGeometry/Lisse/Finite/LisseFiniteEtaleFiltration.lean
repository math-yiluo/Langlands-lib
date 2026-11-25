/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Coinvariants
import WeilConjectures.AlgebraicGeometry.Sites.ModulePointFunctions
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteRingTorsorModuleDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteRingTorsorModuleComparisons
import WeilConjectures.ConstructibleSheaf.FiniteSetMonodromyTorsor
import WeilConjectures.ConstructibleSheaf.ConnectedTorsorSubgroupQuotient
import WeilConjectures.ConstructibleSheaf.ModuleConstantOfSetPullback
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
import WeilConjectures.RepresentationTheory.PrimaryPGroupFiltration

/-!
# Prime-to-primary finite étale filtration covers

## References

* Stacks Project, Tags 0GJ0 and 0DV5 (3), with componentwise assembly on an affine Noetherian base
* Stacks Project, Tags 0GJ0, 0DV5 (3), 0DV6 and 0GIZ
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem affine_clopen_isAffineOpen
    {X : Scheme.{u}} [IsAffine X] (U : X.Opens) (hU : IsClosed (U : Set X)) :
    IsAffineOpen U := by
  have : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion U.ι (by simpa using hU)
  exact isAffine_of_isAffineHom U.ι

private theorem affine_noetherian_components
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    ∃ (k : ℕ) (U : Fin k → (Spec (.of A)).Opens),
      (∀ i, IsAffineOpen (U i) ∧ IsClosed (U i : Set (Spec (.of A))) ∧
        ConnectedSpace (U i).toScheme) ∧
      Pairwise (fun i j ↦ Disjoint (U i) (U j)) ∧
      (⋃ i, (U i : Set (Spec (.of A)))) = Set.univ := by
  classical
  let X := Spec (.of A)
  let k := Nat.card (ConnectedComponents X)
  let e : ConnectedComponents X ≃ Fin k := Finite.equivFin _
  let U (i : Fin k) : X.Opens :=
    ⟨ConnectedComponents.mk ⁻¹' {e.symm i},
      (isOpen_discrete {e.symm i}).preimage ConnectedComponents.continuous_coe⟩
  refine ⟨k, U, ?_, ?_, ?_⟩
  · intro i
    have hclosed : IsClosed (U i : Set X) :=
      (isClosed_discrete {e.symm i}).preimage ConnectedComponents.continuous_coe
    refine ⟨affine_clopen_isAffineOpen (U i) hclosed, hclosed, ?_⟩
    obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (e.symm i)
    have heq : (U i : Set X) = connectedComponent x := by
      change ConnectedComponents.mk ⁻¹' {e.symm i} = _
      rw [← hx]
      exact connectedComponents_preimage_singleton
    exact isConnected_iff_connectedSpace.mp (heq ▸ isConnected_connectedComponent)
  · intro i j hij
    exact TopologicalSpace.Opens.coe_disjoint.mp ((Set.disjoint_singleton.mpr
      (e.symm.injective.ne hij)).preimage ConnectedComponents.mk)
  · apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨e (ConnectedComponents.mk x), by simp [U]⟩

private theorem primary_module_filtration
    (Λ : Type (u + 1)) [CommRing Λ]
    (P : Type u) [Group P] (ℓ : ℕ) (hℓ : ℓ.Prime) (hP : IsPGroup ℓ P)
    (M : Rep.{u + 1} Λ P) [Finite M.V] (hM : IsPGroup ℓ (Multiplicative M.V)) :
    ∃ (r : ℕ) (N : Fin (r + 1) → Submodule Λ M.V),
      Monotone N ∧ N 0 = ⊥ ∧ N (Fin.last r) = ⊤ ∧
      (∀ i g, N i ≤ (N i).comap (M.ρ g)) ∧
      (∀ (i : Fin r) (g : P) (x : M.V), x ∈ N i.succ →
        M.ρ g x - x ∈ N i.castSucc) := by
  let ρ : Representation ℤ P M.V :=
    { toFun := fun g ↦ (M.ρ g).restrictScalars ℤ
      map_one' := by ext x; exact congrArg (fun f ↦ f x) M.ρ.map_one
      map_mul' := by intro g h; ext x; exact congrArg (fun f ↦ f x) (M.ρ.map_mul g h) }
  obtain ⟨r, W, hmono, hzero, htop, hstable, hstep⟩ :=
    Representation.exists_primary_filtration_of_isPGroup P ℓ hℓ hP M.V ρ hM
  let N (i : Fin (r + 1)) := Submodule.span Λ (W i : Set M.V)
  have hN : Monotone N := fun i j hij ↦ Submodule.span_mono (hmono hij)
  refine ⟨r, N, hN, ?_, ?_, ?_, ?_⟩
  · simp [N, hzero]
  · simp [N, htop]
  · intro i g x hx
    change M.ρ g x ∈ N i
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hstable i g x hx)
    | zero => simp
    | add x y _ _ hx hy => simpa using (N i).add_mem hx hy
    | smul a x _ hx => simpa using (N i).smul_mem a hx
  · intro i g x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ((hstep i x hx).2 g)
    | zero => simp
    | add x y _ _ hx hy =>
      simpa only [map_add, add_sub_add_comm] using (N i.castSucc).add_mem hx hy
    | smul a x _ hx =>
      simpa only [map_smul, smul_sub] using (N i.castSucc).smul_mem a hx

private theorem cokernel_inclusion_iso_quotient
    {Λ : Type (u + 1)} [CommRing Λ] {P : Type u} [Group P]
    (M : Rep.{u + 1} Λ P)
    (A B : Submodule Λ M.V) (hA : ∀ g, A ≤ A.comap (M.ρ g))
    (hB : ∀ g, B ≤ B.comap (M.ρ g)) (hle : A ≤ B) :
    let S := M.subrepresentation A hA
    let S' := M.subrepresentation B hB
    let f : S ⟶ S' := Rep.ofHom ⟨Submodule.inclusion hle, fun _ ↦ rfl⟩
    let K := A.comap B.subtype
    let hK : ∀ g, K ≤ K.comap (S'.ρ g) := fun g _x hx ↦ hA g hx
    Nonempty (cokernel f ≅ S'.quotient K hK) := by
  intro S S' f K hK
  let q := S'.mkQ K hK
  have hcomp : f ≫ q = 0 := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero K).2 x.property
  let C := ShortComplex.mk f q hcomp
  have hex : C.Exact := by
    rw [← C.exact_map_iff_of_faithful (forget₂ (Rep Λ P) (ModuleCat Λ))]
    rw [ShortComplex.moduleCat_exact_iff]
    change ∀ x : B, K.mkQ x = 0 → ∃ y : A, Submodule.inclusion hle y = x
    intro x hx
    have hx' : x ∈ K := (Submodule.Quotient.mk_eq_zero K).1 hx
    exact ⟨⟨x.val, hx'⟩, Subtype.ext rfl⟩
  have hepi : Epi q := (Rep.epi_iff_surjective q).2 K.mkQ_surjective
  exact ⟨(colimit.isColimit _).coconePointUniqueUpToIso hex.gIsCokernel⟩

private theorem filtration_of_primary_representation
    (Λ : Type (u + 1)) [CommRing Λ]
    (P : Type u) [Group P] (ℓ : ℕ) (hℓ : ℓ.Prime) (hP : IsPGroup ℓ P)
    (M : Rep.{u + 1} Λ P) [Finite M.V] (hM : IsPGroup ℓ (Multiplicative M.V))
    {X : Scheme.{u}}
    (T : Rep.{u + 1} Λ P ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (Z : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (e : T.obj M ≅ Z)
    (hconstant : ∀ B : ModuleCat.{u + 1} Λ, Finite B →
      Nonempty (T.obj (Rep.trivial Λ P B) ≅
        (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj B)) :
    ∃ (r : ℕ) (c : Fin (r + 1) → Subobject Z) (hc : Monotone c),
      IsZero (c 0 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ∧
      c (Fin.last r) = ⊤ ∧
      ∀ i : Fin r, ∃ B : ModuleCat.{u + 1} Λ, Finite B ∧
        Nonempty (cokernel (Subobject.ofLE (c i.castSucc) (c i.succ)
          (hc (Fin.castSucc_le_succ i))) ≅
            (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj B) := by
  classical
  obtain ⟨r, N, hmono, hzero, htop, hstable, hstep⟩ :=
    primary_module_filtration Λ P ℓ hℓ hP M hM
  let W (i : Fin (r + 1)) := M.subrepresentation (N i) (hstable i)
  let j (i : Fin (r + 1)) : W i ⟶ M := M.subtype (N i) (hstable i)
  have hj (i) : Mono (j i) := (Rep.mono_iff_injective (j i)).2 Subtype.val_injective
  let f (i j : Fin (r + 1)) (h : i ≤ j) : W i ⟶ W j :=
    Rep.ofHom ⟨Submodule.inclusion (hmono h), fun _ ↦ rfl⟩
  have hfac (i j' : Fin (r + 1)) (h : i ≤ j') : f i j' h ≫ j j' = j i := by
    ext x
    rfl
  let a (i : Fin (r + 1)) := T.map (j i) ≫ e.hom
  have ha (i) : Mono (a i) := by dsimp [a]; infer_instance
  let c (i : Fin (r + 1)) : Subobject Z := Subobject.mk (a i)
  have hc : Monotone c := by
    intro i j hij
    apply Subobject.mk_le_mk_of_comm (T.map (f i j hij))
    simp only [a, ← Category.assoc, ← T.map_comp, hfac]
  have hWzero : IsZero (W 0) := by
    apply (Rep.isZero_iff (W 0)).mpr
    change Subsingleton (N 0)
    rw [hzero]
    infer_instance
  have hjlast : IsIso (j (Fin.last r)) := by
    have : Epi (j (Fin.last r)) := (Rep.epi_iff_surjective _).2 (by
      intro x
      exact ⟨⟨x, htop ▸ Submodule.mem_top⟩, rfl⟩)
    exact isIso_of_mono_of_epi _
  refine ⟨r, c, hc, ?_, ?_, ?_⟩
  · exact (T.map_isZero hWzero).of_iso (Subobject.underlyingIso (a 0))
  · exact Subobject.mk_eq_top_of_isIso (a (Fin.last r))
  · intro i
    let K := (N i.castSucc).comap (N i.succ).subtype
    have hK : ∀ g, K ≤ K.comap ((W i.succ).ρ g) :=
      fun g _x hx ↦ hstable i.castSucc g hx
    let Q := (W i.succ).quotient K hK
    have hQfin : Finite Q.V := Finite.of_surjective K.mkQ K.mkQ_surjective
    have htriv (g : P) (x : Q.V) : Q.ρ g x = x := by
      obtain ⟨x, rfl⟩ := K.mkQ_surjective x
      change K.mkQ ((W i.succ).ρ g x) = K.mkQ x
      apply (Submodule.Quotient.eq K).2
      exact hstep i g x.val x.property
    let eQ : Q ≅ Rep.trivial Λ P Q.V := Rep.mkIso
      (Representation.Equiv.mk (LinearEquiv.refl Λ Q.V) (fun g ↦ by
        apply LinearMap.ext
        intro x
        exact htriv g x))
    obtain ⟨eqt⟩ := cokernel_inclusion_iso_quotient M (N i.castSucc) (N i.succ)
      (hstable i.castSucc) (hstable i.succ) (hmono (Fin.castSucc_le_succ i))
    let B : ModuleCat.{u + 1} Λ := ModuleCat.of Λ Q.V
    obtain ⟨econstant⟩ := hconstant B hQfin
    let eck : cokernel (Subobject.ofLE (c i.castSucc) (c i.succ)
        (hc (Fin.castSucc_le_succ i))) ≅
        cokernel (T.map (f i.castSucc i.succ (Fin.castSucc_le_succ i))) :=
      cokernel.mapIso _ _ (Subobject.underlyingIso (a i.castSucc))
        (Subobject.underlyingIso (a i.succ)) (by
          apply (cancel_mono (a i.succ)).1
          simp only [c, Category.assoc, Subobject.ofLE_arrow,
            Subobject.underlyingIso_hom_comp_eq_mk]
          change (Subobject.mk (a i.castSucc)).arrow =
            (Subobject.underlyingIso (a i.castSucc)).hom ≫
              T.map (f i.castSucc i.succ (Fin.castSucc_le_succ i)) ≫
                (T.map (j i.succ) ≫ e.hom)
          rw [← Category.assoc (T.map _), ← T.map_comp, hfac _ _ (Fin.castSucc_le_succ i)]
          exact (Subobject.underlyingIso_hom_comp_eq_mk _).symm)
    exact ⟨B, hQfin, ⟨eck ≪≫ (PreservesCokernel.iso T _).symm ≪≫
      T.mapIso eqt ≪≫ T.mapIso eQ ≪≫ econstant⟩⟩

private theorem balanced_coproduct_fiber
    {X : Scheme.{u}} {k : ℕ} (U : Fin k → X.Opens)
    (hdisj : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (V : Fin k → Scheme.{u}) (v : ∀ i, V i ⟶ (U i).toScheme)
    (c : Fin k → ℕ) (j : Fin k)
    {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ (U j).toScheme) :
    Nat.card ((Sigma.desc (fun a : (i : Fin k) × Fin (c i) ↦
      v a.1 ≫ (U a.1).ι)).GeometricFiber (s ≫ (U j).ι)) =
        c j * Nat.card ((v j).GeometricFiber s) := by
  classical
  let I := (i : Fin k) × Fin (c i)
  let Y (a : I) := V a.1
  let g : (∐ Y) ⟶ X := Sigma.desc fun a ↦ v a.1 ≫ (U a.1).ι
  let f : Fin (c j) × (v j).GeometricFiber s → g.GeometricFiber (s ≫ (U j).ι) :=
    fun a ↦ ⟨a.2.val ≫ Sigma.ι Y ⟨j, a.1⟩, by
      simp only [Category.assoc, g, Sigma.ι_comp_desc]
      rw [← Category.assoc, a.2.property]⟩
  have hinj : Function.Injective f := by
    rintro ⟨b, x⟩ ⟨b', x'⟩ h
    have heq := congrArg (fun a : g.GeometricFiber (s ≫ (U j).ι) ↦ a.val) h
    have hpts := congrArg (fun a ↦ a default) heq
    have hidx := (sigmaι_eq_iff Y ⟨j, b⟩ ⟨j, b'⟩ _ _).mp hpts
    have hidx' : (⟨j, b⟩ : I) = ⟨j, b'⟩ := congrArg Sigma.fst hidx
    have hb : b = b' := by simpa using (Sigma.mk.inj hidx').2
    subst b'
    have hx : x.val = x'.val := (cancel_mono (Sigma.ι Y ⟨j, b⟩)).mp heq
    exact Prod.ext rfl (Subtype.ext hx)
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨⟨i, b⟩, t, ht⟩ := exists_comp_sigmaι_eq_of_subsingleton a.val
    have hcomp : t ≫ v i ≫ (U i).ι = s ≫ (U j).ι := by
      rw [← a.property, ← ht, Category.assoc]
      simp only [g, Sigma.ι_comp_desc]
    have hij : i = j := by
      by_contra hij
      have hp := congrArg (fun t ↦ t default) hcomp
      have hi : ((U i).ι) ((t ≫ v i) default) ∈ U i := ((t ≫ v i) default).property
      have hj : ((U j).ι) (s default) ∈ U j := (s default).property
      exact Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr
        (hdisj hij)) hi (by simpa only [Scheme.Hom.comp_apply] using hp ▸ hj)
    subst i
    have hts : t ≫ v j = s := (cancel_mono (U j).ι).mp (by
      simpa only [Category.assoc] using hcomp)
    exact ⟨⟨b, ⟨t, hts⟩⟩, Subtype.ext ht⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_fin]

private theorem assemble_component_covers
    {X : Scheme.{u}} {k : ℕ} (U : Fin k → X.Opens)
    (haff : ∀ i, IsAffineOpen (U i)) (hclosed : ∀ i, IsClosed (U i : Set X))
    (hdisj : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (hcover : (⋃ i, (U i : Set X)) = Set.univ)
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (V : Fin k → Scheme.{u}) (v : ∀ i, V i ⟶ (U i).toScheme)
    [∀ i, IsFinite (v i)] [∀ i, Etale (v i)] [∀ i, Surjective (v i)]
    (d : Fin k → ℕ) (hpos : ∀ i, 1 ≤ d i) (hprime : ∀ i, ¬ ℓ ∣ d i)
    (hdegree : ∀ i (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ (U i).toScheme), Nat.card ((v i).GeometricFiber s) = d i) :
    ∃ (T : Scheme.{u}) (g : T ⟶ X), IsFinite g ∧ Etale g ∧ Surjective g ∧
      ∃ D : ℕ, 1 ≤ D ∧ ¬ ℓ ∣ D ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
          Nat.card (g.GeometricFiber s) = D) ∧
        ∃ (m : ℕ) (W : Fin m → T.Opens),
          (∀ a, IsAffineOpen (W a) ∧ IsClosed (W a : Set T)) ∧
          Pairwise (fun a b ↦ Disjoint (W a) (W b)) ∧
          (⋃ a, (W a : Set T)) = Set.univ ∧
          ∀ a, ∃ (i : Fin k) (e : (W a).toScheme ≅ V i),
            e.hom ≫ v i ≫ (U i).ι = (W a).ι ≫ g := by
  classical
  let c (i : Fin k) := ∏ j ∈ Finset.univ.erase i, d j
  let D := ∏ i, d i
  have hcpos (i) : 0 < c i := Finset.prod_pos (fun j _ ↦ hpos j)
  have hDpos : 1 ≤ D := by
    change 0 < D
    exact Finset.prod_pos (fun i _ ↦ hpos i)
  have hDprime : ¬ ℓ ∣ D := by
    intro h
    obtain ⟨i, _, hi⟩ := (hℓ.prime.dvd_finsetProd_iff _).mp h
    exact hprime i hi
  have hmul (i) : c i * d i = D := Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  let I := (i : Fin k) × Fin (c i)
  let Y (a : I) := V a.1
  let T := ∐ Y
  let g : T ⟶ X := Sigma.desc fun a ↦ v a.1 ≫ (U a.1).ι
  have hclimm (i) : IsClosedImmersion (U i).ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa using hclosed i)
  have hf (a : I) : IsFinite (v a.1 ≫ (U a.1).ι) := by infer_instance
  have hgfin : IsFinite g := by dsimp [g]; infer_instance
  have hget : Etale g := IsZariskiLocalAtSource.sigmaDesc (fun _ ↦ inferInstance)
  have hgsurj : Surjective g := by
    constructor
    intro x
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
    obtain ⟨y, hy⟩ := (show Surjective (v i) from inferInstance).surj ⟨x, hxi⟩
    refine ⟨Sigma.ι Y ⟨i, ⟨0, hcpos i⟩⟩ y, ?_⟩
    change (Sigma.ι Y ⟨i, ⟨0, hcpos i⟩⟩ ≫ g) y = x
    simp only [g, Sigma.ι_comp_desc, Scheme.Hom.comp_apply]
    exact congrArg Subtype.val hy
  have hgfiber (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :
      Nat.card (g.GeometricFiber s) = D := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ (s default))
    let t : Spec (.of Ω) ⟶ (U i).toScheme :=
      IsOpenImmersion.lift (U i).ι s (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨x, rfl⟩
        rw [Subsingleton.elim x default]
        exact hi)
    have ht : t ≫ (U i).ι = s := IsOpenImmersion.lift_fac _ _ _
    rw [← ht, balanced_coproduct_fiber U hdisj V v c i t, hdegree, hmul]
  have hYaff (a : I) : IsAffine (Y a) := by
    let : IsAffine (U a.1).toScheme := haff a.1
    exact isAffine_of_isAffineHom (v a.1)
  let O (a : I) : T.Opens := (Sigma.ι Y a).opensRange
  have hOdisj : Pairwise (fun a b ↦ Disjoint (O a) (O b)) :=
    fun a b hab ↦ disjoint_opensRange_sigmaι Y a b hab
  have hOcover : (⋃ a, (O a : Set T)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, y, hy⟩ := (sigmaOpenCover Y).exists_eq x
    exact Set.mem_iUnion.mpr ⟨a, y, hy⟩
  have hOclosed (a : I) : IsClosed (O a : Set T) := by
    have heq : (O a : Set T)ᶜ = ⋃ b : {b : I // b ≠ a}, (O b.val : Set T) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion]
      constructor
      · intro hx
        obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (hOcover.symm ▸ Set.mem_univ x)
        exact ⟨⟨b, fun h ↦ hx (h ▸ hb)⟩, hb⟩
      · rintro ⟨b, hb⟩ ha
        exact Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr
          (hOdisj b.property)) hb ha
    rw [← isOpen_compl_iff, heq]
    exact isOpen_iUnion fun b ↦ (O b.val).isOpen
  let m := Nat.card I
  let q : I ≃ Fin m := Finite.equivFin I
  refine ⟨T, g, hgfin, hget, hgsurj, D, hDpos, hDprime, hgfiber,
    m, fun a ↦ O (q.symm a), ?_, ?_, ?_, ?_⟩
  · intro a
    refine ⟨?_, hOclosed _⟩
    simpa only [Scheme.Hom.image_top_eq_opensRange] using
      (isAffineOpen_top (Y (q.symm a))).image_of_isOpenImmersion (Sigma.ι Y (q.symm a))
  · intro a b hab
    exact hOdisj (q.symm.injective.ne hab)
  · rw [← hOcover]
    exact q.symm.surjective.iUnion_comp (fun a ↦ (O a : Set T))
  · intro a
    let b := q.symm a
    let e : (O b).toScheme ≅ Y b :=
      IsOpenImmersion.isoOfRangeEq (O b).ι (Sigma.ι Y b)
        (by rw [Scheme.Opens.range_ι]; rfl)
    refine ⟨b.1, e, ?_⟩
    rw [← Sigma.ι_comp_desc (fun a : I ↦ v a.1 ≫ (U a.1).ι) b,
      ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]

private theorem representation_stalks_of_torsor_pullback
    {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) X)
    (T : Rep.{u + 1} Λ P ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (eπ : T ⋙ upperStar (ModuleCat.{u + 1} Λ) c.π ≅
      forget₂ (Rep.{u + 1} Λ P) (ModuleCat.{u + 1} Λ) ⋙
        constantSheaf c.P.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Nonempty (T ⋙ (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) ≅
      forget₂ (Rep.{u + 1} Λ P) (ModuleCat.{u + 1} Λ)) := by
  classical
  let C := ModuleCat.{u + 1} Λ
  let := c.etale
  have : PreservesFilteredColimitsOfSize.{u, u} (forget C) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨y, hy⟩ := c.surjective.surj (s default)
  obtain ⟨t, ht, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed c.π s y
    (by simpa using hy)
  let S := (Scheme.pointSmallEtale t).sheafFiber (A := C)
  let U := forget₂ (Rep.{u + 1} Λ P) C
  let ebase : upperStar C c.π ⋙ S ≅ (Scheme.pointSmallEtale s).sheafFiber (A := C) :=
    upperStarCompSheafFiberIso C c.π t ≪≫ eqToIso (by rw [ht])
  exact ⟨Functor.isoWhiskerLeft T ebase.symm ≪≫
    (Functor.associator T (upperStar C c.π) S).symm ≪≫
    Functor.isoWhiskerRight eπ S ≪≫
    Functor.associator U (constantSheaf c.P.smallEtaleTopology C) S ≪≫
    Functor.isoWhiskerLeft U
      ((Scheme.pointSmallEtale t).constantSheafCompSheafFiberIso c.P.smallEtaleTopology C) ≪≫
    Functor.rightUnitor U⟩

private theorem exact_of_representation_stalks
    {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]
    (P : Type u) [Group P]
    (T : Rep.{u + 1} Λ P ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hstalk : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nonempty (T ⋙ (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) ≅
        forget₂ (Rep.{u + 1} Λ P) (ModuleCat.{u + 1} Λ))) :
    PreservesFiniteLimits T ∧ PreservesFiniteColimits T := by
  let C := ModuleCat.{u + 1} Λ
  let I := (ObjectProperty.ofObj X.uliftPointSmallEtale).FullSubcategory
  let S (Φ : I) := Φ.obj.sheafFiber (A := C)
  have hcomp (Φ : I) : PreservesFiniteLimits (T ⋙ S Φ) ∧
      PreservesFiniteColimits (T ⋙ S Φ) := by
    obtain ⟨Φ, ⟨x⟩⟩ := Φ
    obtain ⟨τ⟩ := hstalk (AlgebraicClosure (X.residueField x)) (X.algClosurePoint x)
    let e : T ⋙ (X.uliftPointSmallEtale x).sheafFiber (A := C) ≅
        forget₂ (Rep.{u + 1} Λ P) C :=
      Functor.isoWhiskerLeft T
        ((Scheme.pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso C) ≪≫ τ
    exact ⟨preservesFiniteLimits_of_natIso e.symm,
      preservesFiniteColimits_of_natIso e.symm⟩
  have hcons := Scheme.jointlyReflectIsomorphisms_ulift_pointSmallEtale X C
  constructor
  · constructor
    intro J _ _
    constructor
    intro K
    apply preservesLimit_of_preserves_limit_cone (limit.isLimit K)
    apply hcons.jointlyReflectsLimit
    intro Φ
    have : PreservesFiniteLimits (T ⋙ S Φ) := (hcomp Φ).1
    exact isLimitOfPreserves (T ⋙ S Φ) (limit.isLimit K)
  · constructor
    intro J _ _
    constructor
    intro K
    apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
    apply hcons.jointlyReflectsColimit
    intro Φ
    have : PreservesFiniteColimits (T ⋙ S Φ) := (hcomp Φ).2
    exact isColimitOfPreserves (T ⋙ S Φ) (colimit.isColimit K)

private theorem finite_constant_of_unit
    {X : Scheme.{u}} [ConnectedSpace X]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (P : Type u) [Group P]
    (T : Rep.{u + 1} Λ P ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (eunit : T.obj (Rep.trivial Λ P Λ) ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))
    (hstalk : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nonempty (T ⋙ (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) ≅
        forget₂ (Rep.{u + 1} Λ P) (ModuleCat.{u + 1} Λ)))
    (B : ModuleCat.{u + 1} Λ) (hB : Finite B) :
    Nonempty (T.obj (Rep.trivial Λ P B) ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj B) := by
  classical
  let C := ModuleCat.{u + 1} Λ
  have : PreservesFilteredColimitsOfSize.{u, u} (forget C) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let K := constantSheaf X.smallEtaleTopology C
  let Q : ObjectProperty (Sheaf X.smallEtaleTopology C) := K.essImage
  have : PreservesLimits (Rep.trivialFunctor.{u + 1} Λ P) :=
    (Rep.coinvariantsAdjunction Λ P).rightAdjoint_preservesLimits
  have : PreservesColimits (Rep.trivialFunctor.{u + 1} Λ P) :=
    (Rep.invariantsAdjunction Λ P).leftAdjoint_preservesColimits
  let H := Rep.trivialFunctor.{u + 1} Λ P ⋙ T
  have : PreservesFiniteLimits H := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits H := comp_preservesFiniteColimits _ _
  have hunit : Q (H.obj (ModuleCat.of Λ Λ)) := ⟨ModuleCat.of Λ Λ, ⟨eunit.symm⟩⟩
  have hfree (n : ℕ) : Q (H.obj (ModuleCat.of Λ (Fin n → Λ))) := by
    exact Q.prop_of_isLimit
      (isLimitOfPreserves H (ModuleCat.productConeIsLimit
        (fun _ : Fin n ↦ ModuleCat.of Λ Λ))) (fun _ ↦ hunit)
  have : Module.Finite Λ B := Module.Finite.of_finite
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' Λ B
  let Kπ := LinearMap.ker π
  have : Module.Finite Λ Kπ := Module.Finite.of_finite
  obtain ⟨m, r, hr⟩ := Module.Finite.exists_fin' Λ Kπ
  let f : ModuleCat.of Λ (Fin m → Λ) ⟶ ModuleCat.of Λ (Fin n → Λ) :=
    ModuleCat.ofHom (Kπ.subtype.comp r)
  let q : ModuleCat.of Λ (Fin n → Λ) ⟶ B := ModuleCat.ofHom π
  have hzero : f ≫ q = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (r x).property
  let SC := ShortComplex.mk f q hzero
  have hex : SC.Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    obtain ⟨y, hy⟩ := hr ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  have : Epi q := (ModuleCat.epi_iff_surjective q).2 hπ
  have hconst : Q (H.obj B) := Q.prop_of_isColimit
    (isColimitOfPreserves H hex.gIsCokernel) (by
      intro j
      cases j
      · exact hfree m
      · exact hfree n)
  obtain ⟨B', ⟨eB⟩⟩ := hconst
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let s := X.algClosurePoint x
  let S := (Scheme.pointSmallEtale s).sheafFiber (A := C)
  obtain ⟨τ⟩ := hstalk (AlgebraicClosure (X.residueField x)) s
  let evalues : B' ≅ B :=
    ((Scheme.pointSmallEtale s).sheafFiberConstantSheafIso B').symm ≪≫
      S.mapIso eB ≪≫ τ.app (Rep.trivial Λ P B)
  exact ⟨eB.symm ≪≫ K.mapIso evalues⟩

private theorem finite_primary_representation_of_stalk
    {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {P : Type u} [Group P] (M : Rep.{u + 1} Λ P)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsFiniteSheaf F]
    (ℓ n : ℕ) (hF : (ℓ ^ n) • 𝟙 F = 0)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (e : ModuleCat.of Λ M.V ≅
      ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :
    Finite M.V ∧ IsPGroup ℓ (Multiplicative M.V) := by
  let S := (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  let B := S.obj F
  have : S.Additive := (Scheme.pointSmallEtale s).sheafFiber_additive
  have : Module.Finite Λ B := (ModuleCat.isFinitelyGenerated_iff B).mp
    (Scheme.IsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω s)
  have : Finite B := Module.finite_of_finite Λ
  have hfinite : Finite M.V := Finite.of_equiv B e.toLinearEquiv.symm.toEquiv
  have hB : (ℓ ^ n) • 𝟙 B = 0 := by
    have heq := congrArg S.map hF
    rw [Functor.map_nsmul, S.map_id, Functor.map_zero] at heq
    exact heq
  have hM : (ℓ ^ n) • 𝟙 (ModuleCat.of Λ M.V) = 0 := by
    apply (cancel_mono e.hom).mp
    rw [Preadditive.nsmul_comp, Category.id_comp, zero_comp]
    rw [← Category.comp_id e.hom, ← Preadditive.comp_nsmul, hB, comp_zero]
  refine ⟨hfinite, isPGroup_iff_pow_pow_eq_one.mpr ?_⟩
  intro x
  refine ⟨n, ?_⟩
  have hx := congrArg (fun f : ModuleCat.of Λ M.V ⟶ ModuleCat.of Λ M.V ↦ f x.toAdd) hM
  change (ℓ ^ n) • x.toAdd = 0 at hx
  rw [← ofAdd_toAdd x, ← ofAdd_nsmul, hx, ofAdd_zero]

private theorem connected_sylow_sheaf_data
    {X : Scheme.{u}} [ConnectedSpace X]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf F]
    (ℓ n : ℕ) (hℓ : ℓ.Prime) (hF : (ℓ ^ n) • 𝟙 F = 0) :
    ∃ (V : Scheme.{u}) (v : V ⟶ X) (_ : IsFinite v) (_ : Etale v)
      (_ : Surjective v) (d : ℕ), 1 ≤ d ∧ ¬ ℓ ∣ d ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X),
        Nat.card (v.GeometricFiber s) = d) ∧
      ∃ (P : Type u) (_ : Group P), IsPGroup ℓ P ∧
        ∃ (M : Rep.{u + 1} Λ P) (_ : Finite M.V),
          IsPGroup ℓ (Multiplicative M.V) ∧
          ∃ (T : Rep.{u + 1} Λ P ⥤ Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
            (_ : T.Additive) (_ : PreservesFiniteLimits T) (_ : PreservesFiniteColimits T),
            Nonempty (T.obj M ≅ (upperStar (ModuleCat.{u + 1} Λ) v).obj F) ∧
            ∀ B : ModuleCat.{u + 1} Λ, Finite B →
              Nonempty (T.obj (Rep.trivial Λ P B) ≅
                (constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj B) := by
  classical
  let : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨datum, hdatum⟩ := (Scheme.finite_locally_constant_module_values_iff F).1.mpr
    (inferInstance : Scheme.IsFiniteLocallyConstantSheaf F)
  have hlisse : Scheme.IsLisseModuleSheaf F := ⟨datum.cover, hdatum⟩
  have hsets := (Scheme.lisseModuleSheaf_iff_underlying_finiteLocallyConstant F).mp hlisse
  obtain ⟨Q, hQ, hQfin, c, hconn, hconstant⟩ :=
    Scheme.exists_connected_torsor_constant_set_pullback
      ((sheafForget X.smallEtaleTopology).obj F) hsets
  let := hQ
  let := hQfin
  let := hconn
  have hmodule := Scheme.module_pullback_isConstant_of_set_pullback Λ c.π F hconstant
  let := hmodule
  obtain ⟨A, ⟨α⟩⟩ := ((upperStar (ModuleCat.{u + 1} Λ) c.π).obj F).mem_essImage_of_isConstant
  let H : Sylow ℓ Q := Classical.choice inferInstance
  obtain ⟨V, v, hvfin, hvet, hV, hdegree, cH, hcH, e, he⟩ :=
    c.exists_connected_subgroup_quotient Q H.toSubgroup
  let := hvfin
  let := hvet
  let := hV
  let := hcH
  let C := ModuleCat.{u + 1} Λ
  have htriv : Nonempty ((upperStar C cH.π).obj ((upperStar C v).obj F) ≅
      (constantSheaf cH.P.smallEtaleTopology C).obj A) := by
    refine ⟨((upperStarComp C cH.π v).app F).symm ≪≫
      (upperStarComp C e.hom c.π (cH.π ≫ v) he.symm).app F ≪≫
      (upperStar C e.hom).mapIso α.symm ≪≫
      (Scheme.upperStarConstantSheafIso C e.hom).app A⟩
  obtain ⟨M, ⟨eF⟩⟩ :=
    cH.exists_finiteRing_module_descent Λ H.toSubgroup ((upperStar C v).obj F) A htriv
  obtain ⟨⟨eπ⟩, ⟨eunit⟩⟩ := cH.associatedModuleFunctorOver_comparisons Λ
  let T := cH.associatedModuleFunctorOver Λ
  have hTadd : T.Additive := inferInstance
  have hTstalk := representation_stalks_of_torsor_pullback Λ H.toSubgroup cH T eπ
  obtain ⟨hTlim, hTcolim⟩ := exact_of_representation_stalks Λ H.toSubgroup T hTstalk
  let := hTadd
  let := hTlim
  let := hTcolim
  obtain ⟨x⟩ := (inferInstance : Nonempty V)
  let Ω := AlgebraicClosure (V.residueField x)
  let s := V.algClosurePoint x
  obtain ⟨τ⟩ := hTstalk Ω s
  let S := (Scheme.pointSmallEtale s).sheafFiber (A := C)
  let eM : ModuleCat.of Λ M.V ≅ S.obj ((upperStar C v).obj F) :=
    (τ.app M).symm ≪≫ S.mapIso eF
  have : Scheme.IsFiniteSheaf ((upperStar C v).obj F) := Scheme.IsFiniteSheaf.upperStar v F
  have hkill : (ℓ ^ n) • 𝟙 ((upperStar C v).obj F) = 0 := by
    rw [← (upperStar C v).map_id, ← Functor.map_nsmul, hF, Functor.map_zero]
  obtain ⟨hMfin, hMprimary⟩ := finite_primary_representation_of_stalk Λ M
    ((upperStar C v).obj F) ℓ n hkill s eM
  have hvpos : 1 ≤ H.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hvsurj : Surjective v := by
    constructor
    intro z
    obtain ⟨y, hy⟩ := c.surjective.surj z
    refine ⟨cH.π (e.inv y), ?_⟩
    have hw := congrArg (fun f ↦ f (e.inv y)) he
    have hw' : v (cH.π (e.inv y)) = c.π y := by
      simpa only [Scheme.Hom.comp_apply, Scheme.inv_hom_apply] using hw.symm
    exact hw'.trans hy
  refine ⟨V, v, hvfin, hvet, hvsurj, H.index, hvpos, H.not_dvd_index,
    fun Ω _ _ s ↦ hdegree Ω s, H.toSubgroup, inferInstance, H.isPGroup', M, hMfin,
    hMprimary, T, hTadd, hTlim, hTcolim, ⟨eF⟩, ?_⟩
  exact finite_constant_of_unit Λ H.toSubgroup T eunit hTstalk

/-- A finite local system of modules over a finite ring, killed by a positive prime power,
admits a finite étale surjection of constant prime-to-primary degree, and on a finite affine
clopen decomposition of its source the pullback has constant finite-module graded pieces. -/
theorem exists_lisse_finiteEtale_filtration
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsFiniteLocallyConstantSheaf F]
    (ℓ n : ℕ) (hℓ : ℓ.Prime) (hn : 1 ≤ n) (hF : (ℓ ^ n) • 𝟙 F = 0) :
    ∃ (T : Scheme.{u}) (g : T ⟶ Spec (.of A)),
      IsFinite g ∧ Etale g ∧ Surjective g ∧
      ∃ d : ℕ, 1 ≤ d ∧ ¬ ℓ ∣ d ∧
        (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of A)),
          Nat.card (g.GeometricFiber s) = d) ∧
        ∃ (k : ℕ) (U : Fin k → T.Opens),
          (∀ a, IsAffineOpen (U a) ∧ IsClosed (U a : Set T)) ∧
          Pairwise (fun a b => Disjoint (U a) (U b)) ∧
          (⋃ a, (U a : Set T)) = Set.univ ∧
          ∀ a : Fin k, ∃ (r : ℕ)
            (c : Fin (r + 1) → Subobject
              ((upperStar (ModuleCat.{u + 1} Λ) (U a).ι).obj
                ((upperStar (ModuleCat.{u + 1} Λ) g).obj F)))
            (hc : Monotone c),
            IsZero (c 0 : Sheaf (U a).toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ∧
            c (Fin.last r) = ⊤ ∧
            ∀ i : Fin r, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
              Nonempty (cokernel (Subobject.ofLE (c i.castSucc) (c i.succ)
                (hc (Fin.castSucc_le_succ i))) ≅
                  (constantSheaf (U a).toScheme.smallEtaleTopology
                    (ModuleCat.{u + 1} Λ)).obj M) := by
  classical
  have _hn := hn
  let C := ModuleCat.{u + 1} Λ
  obtain ⟨k, U, hU, hdisj, hcover⟩ := affine_noetherian_components A
  let Fi (i : Fin k) := (upperStar C (U i).ι).obj F
  have hdata (i : Fin k) := by
    let : ConnectedSpace (U i).toScheme := (hU i).2.2
    let : Scheme.IsFiniteLocallyConstantSheaf (Fi i) :=
      Scheme.IsFiniteLocallyConstantSheaf.upperStar (U i).ι F
    have hi : (ℓ ^ n) • 𝟙 (Fi i) = 0 := by
      rw [← (upperStar C (U i).ι).map_id, ← Functor.map_nsmul, hF, Functor.map_zero]
    exact connected_sylow_sheaf_data Λ (Fi i) ℓ n hℓ hi
  choose V v hvfin hvet hvsurj d hdpos hdprime hdegree P hP hPprimary
    M hMfin hMprimary T hTadd hTlim hTcolim he hconst using hdata
  let : ∀ i, IsFinite (v i) := hvfin
  let : ∀ i, Etale (v i) := hvet
  let : ∀ i, Surjective (v i) := hvsurj
  obtain ⟨Y, g, hgfin, hget, hgsurj, D, hDpos, hDprime, hDdegree,
    m, W, hW, hWdisj, hWcover, hWiso⟩ :=
    assemble_component_covers U (fun i ↦ (hU i).1) (fun i ↦ (hU i).2.1)
      hdisj hcover ℓ hℓ V v d hdpos hdprime hdegree
  refine ⟨Y, g, hgfin, hget, hgsurj, D, hDpos, hDprime, hDdegree,
    m, W, hW, hWdisj, hWcover, ?_⟩
  intro a
  obtain ⟨i, e, heq⟩ := hWiso a
  let := hP i
  let := hMfin i
  let := hTadd i
  let := hTlim i
  let := hTcolim i
  let S := upperStar C e.hom
  obtain ⟨ei⟩ := he i
  let ei' : (T i ⋙ S).obj (M i) ≅
      (upperStar C (W a).ι).obj ((upperStar C g).obj F) :=
    S.mapIso ei ≪≫ ((upperStarComp C e.hom (v i)).app (Fi i)).symm ≪≫
      ((upperStarComp C (e.hom ≫ v i) (U i).ι).app F).symm ≪≫
      (upperStarComp C (W a).ι g ((e.hom ≫ v i) ≫ (U i).ι)
        (by simpa only [Category.assoc] using heq)).app F
  apply filtration_of_primary_representation Λ (P i) ℓ hℓ (hPprimary i)
    (M i) (hMprimary i) (T i ⋙ S) _ ei'
  intro B hB
  obtain ⟨eb⟩ := hconst i B hB
  exact ⟨S.mapIso eb ≪≫ (Scheme.upperStarConstantSheafIso C e.hom).app B⟩

end AlgebraicGeometry.Etale
