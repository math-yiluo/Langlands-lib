/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StalkRestrictionWithinIso
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Simultaneous lifting of finitely many matrices of free sheaf morphisms

Source: lemma-coherent-base-change-invertible-sheaves--3, finite matrix extension near a point.
(blueprint: lem-pc-finite-free-stalk-finite-matrix-lift)
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def scalarHom {X : Scheme.{u}} (a : Γ(X, ⊤)) :
    Modules.unit X ⟶ Modules.unit X :=
  (SheafOfModules.unitHomEquiv (Modules.unit X)).symm
    ⟨fun U ↦ X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op a, by
      intro U W k
      change X.presheaf.map k (X.presheaf.map _ a) = X.presheaf.map _ a
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl⟩

private lemma scalarHom_app_top {X : Scheme.{u}} (a : Γ(X, ⊤)) :
    Hom.app (scalarHom a) ⊤ (1 : Γ(X, ⊤)) = a := by
  have h := congrArg (fun s ↦ s.val (Opposite.op ⊤))
    ((SheafOfModules.unitHomEquiv (Modules.unit X)).apply_symm_apply
      ⟨fun U ↦ X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op a, by
        intro U W k
        change X.presheaf.map k (X.presheaf.map _ a) = X.presheaf.map _ a
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl⟩)
  exact h.trans (by simp)

private lemma unit_hom_ext_top {X : Scheme.{u}}
    {f g : Modules.unit X ⟶ Modules.unit X}
    (h : Hom.app f ⊤ (1 : Γ(X, ⊤)) = Hom.app g ⊤ (1 : Γ(X, ⊤))) : f = g := by
  apply Modules.hom_ext
  intro U
  ext a
  have hU : Hom.app f U (1 : Γ(X, U)) = Hom.app g U (1 : Γ(X, U)) := by
    have hf := f.mapPresheaf.naturality (homOfLE (show U ≤ ⊤ from le_top)).op
    have hg := g.mapPresheaf.naturality (homOfLE (show U ≤ ⊤ from le_top)).op
    have hf' := congrArg (fun k ↦ k (1 : Γ(X, ⊤))) hf
    have hg' := congrArg (fun k ↦ k (1 : Γ(X, ⊤))) hg
    change Hom.app f U (X.presheaf.map _ (1 : Γ(X, ⊤))) =
      X.presheaf.map _ (Hom.app f ⊤ (1 : Γ(X, ⊤))) at hf'
    change Hom.app g U (X.presheaf.map _ (1 : Γ(X, ⊤))) =
      X.presheaf.map _ (Hom.app g ⊤ (1 : Γ(X, ⊤))) at hg'
    simpa only [map_one] using hf'.trans ((congrArg (X.presheaf.map _) h).trans hg'.symm)
  have hf := Hom.app_smul f (U := U) a (1 : Γ(X, U))
  have hg := Hom.app_smul g (U := U) a (1 : Γ(X, U))
  simp only [smul_eq_mul, mul_one] at hf hg
  exact hf.trans (by rw [hU]; exact hg.symm)

private noncomputable def matrixHom {X : Scheme.{u}} {I J : Type u} [Fintype J]
    (A : Matrix J I Γ(X, ⊤)) :
    SheafOfModules.free (R := X.ringCatSheaf) I ⟶ SheafOfModules.free J :=
  Sigma.desc fun i ↦ ∑ j, scalarHom (A j i) ≫ SheafOfModules.ιFree j

set_option backward.isDefEq.respectTransparency false in
private lemma freeMatrix_matrixHom {X : Scheme.{u}} {I J : Type u} [Fintype J]
    [DecidableEq J] (A : Matrix J I Γ(X, ⊤)) : freeMatrix (matrixHom A) = A := by
  ext j i
  change Hom.app (SheafOfModules.ιFree i ≫ matrixHom A ≫ freeπ j) ⊤ (1 : Γ(X, ⊤)) = _
  have h : SheafOfModules.ιFree i ≫ matrixHom A ≫ freeπ j = scalarHom (A j i) := by
    have hi : SheafOfModules.ιFree i ≫ matrixHom A =
        ∑ k : J, scalarHom (A k i) ≫ SheafOfModules.ιFree k := Sigma.ι_comp_desc _ i
    rw [← Category.assoc, hi, Preadditive.sum_comp]
    simp only [Category.assoc, ιFree_freeπ]
    rw [Finset.sum_eq_single j]
    · rw [ite_eq_left rfl, Category.comp_id]
    · intro k _ hkj
      rw [ite_eq_right hkj, comp_zero]
    · intro h
      exact (h (Finset.mem_univ j)).elim
  rw [h, scalarHom_app_top]

private lemma freeMatrix_injective {X : Scheme.{u}} {I J : Type u} [Finite J]
    [DecidableEq J] : Function.Injective
      (freeMatrix (X := X) (I := I) (J := J)) := by
  let := Fintype.ofFinite J
  intro f g h
  apply free_hom_ext
  intro i
  calc
    SheafOfModules.ιFree i ≫ f =
        (SheafOfModules.ιFree i ≫ f) ≫ ∑ j : J, freeπ j ≫ SheafOfModules.ιFree j := by
      rw [sum_freeπ_ιFree, Category.comp_id]
    _ = (SheafOfModules.ιFree i ≫ g) ≫
        ∑ j : J, freeπ j ≫ SheafOfModules.ιFree j := by
      simp only [Preadditive.comp_sum, ← Category.assoc]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      apply unit_hom_ext_top
      exact congrFun (congrFun h j) i
    _ = SheafOfModules.ιFree i ≫ g := by rw [sum_freeπ_ιFree, Category.comp_id]

private lemma unit_hom_comm {X : Scheme.{u}}
    (f g : Modules.unit X ⟶ Modules.unit X) : f ≫ g = g ≫ f := by
  apply unit_hom_ext_top
  change Hom.app g ⊤ (Hom.app f ⊤ (1 : Γ(X, ⊤))) =
    Hom.app f ⊤ (Hom.app g ⊤ (1 : Γ(X, ⊤)))
  let a : Γ(X, ⊤) := Hom.app f ⊤ (1 : Γ(X, ⊤))
  let b : Γ(X, ⊤) := Hom.app g ⊤ (1 : Γ(X, ⊤))
  calc
    (Hom.app g ⊤ a : Γ(X, ⊤)) = a * b := unit_hom_app_top g a
    _ = b * a := mul_comm a b
    _ = Hom.app f ⊤ b := (unit_hom_app_top f b).symm

private lemma free_hom_ext_coordinates {X : Scheme.{u}} {I J : Type u} [Finite J]
    [DecidableEq J] {f g : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      SheafOfModules.free J}
    (h : ∀ i j, SheafOfModules.ιFree i ≫ f ≫ freeπ j =
      SheafOfModules.ιFree i ≫ g ≫ freeπ j) : f = g := by
  apply freeMatrix_injective
  ext j i
  exact congrArg (fun k : Modules.unit X ⟶ Modules.unit X ↦ Hom.app k ⊤ (1 : Γ(X, ⊤))) (h i j)

-- A common scalar action commutes with every matrix over the commutative structure ring.
private lemma scalar_naturality {X : Scheme.{u}} {I J : Type u} [Finite J]
    (c : Modules.unit X ⟶ Modules.unit X)
    (a : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ SheafOfModules.free I)
    (b : SheafOfModules.free (R := X.ringCatSheaf) J ⟶ SheafOfModules.free J)
    (ha : ∀ i, SheafOfModules.ιFree i ≫ a = c ≫ SheafOfModules.ιFree i)
    (hb : ∀ j, SheafOfModules.ιFree j ≫ b = c ≫ SheafOfModules.ιFree j)
    (f : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ SheafOfModules.free J) :
    a ≫ f = f ≫ b := by
  classical
  have hπ (j : J) : b ≫ freeπ j = freeπ j ≫ c := by
    apply free_hom_ext
    intro k
    rw [← Category.assoc, hb k, Category.assoc, ιFree_freeπ,
      ← Category.assoc, ιFree_freeπ]
    split_ifs <;> simp
  apply free_hom_ext_coordinates
  intro i j
  simp only [Category.assoc]
  rw [reassoc_of% (ha i), hπ j]
  simpa only [Category.assoc] using
    unit_hom_comm c (SheafOfModules.ιFree i ≫ f ≫ freeπ j)

-- Naturality on the free inclusions makes the discrepancy of two choices of bases
-- diagonal with the same scalar in every position. Thus conjugation cancels it.
private lemma free_conjugate_comparison {X Z : Scheme.{u}}
    (F G : X.Modules ⥤ Z.Modules) (e : F ≅ G)
    (a₀ : F.obj (Modules.unit X) ≅ Modules.unit Z)
    (b₀ : G.obj (Modules.unit X) ≅ Modules.unit Z)
    (a : ∀ K : Type u, F.obj (SheafOfModules.free K) ≅ SheafOfModules.free K)
    (b : ∀ K : Type u, G.obj (SheafOfModules.free K) ≅ SheafOfModules.free K)
    (ha : ∀ (K : Type u) (i : K), F.map (SheafOfModules.ιFree i) ≫ (a K).hom =
      a₀.hom ≫ SheafOfModules.ιFree i)
    (hb : ∀ (K : Type u) (i : K), G.map (SheafOfModules.ιFree i) ≫ (b K).hom =
      b₀.hom ≫ SheafOfModules.ιFree i)
    {I J : Type u} [Finite J]
    (f : G.obj (SheafOfModules.free I) ⟶ G.obj (SheafOfModules.free J)) :
    (a I).inv ≫ (e.app _).hom ≫ f ≫ (e.app _).inv ≫ (a J).hom =
      (b I).inv ≫ f ≫ (b J).hom := by
  let c (K : Type u) := (a K).symm ≪≫ e.app (SheafOfModules.free K) ≪≫ b K
  let c₀ := a₀.symm ≪≫ e.app (Modules.unit X) ≪≫ b₀
  have hι (K : Type u) (i : K) :
      SheafOfModules.ιFree i ≫ (c K).hom = c₀.hom ≫ SheafOfModules.ιFree i := by
    have hai : SheafOfModules.ιFree i ≫ (a K).inv =
        a₀.inv ≫ F.map (SheafOfModules.ιFree i) := by
      rw [Iso.comp_inv_eq, Category.assoc, ha, Iso.inv_hom_id_assoc]
    dsimp only [c, c₀, Iso.trans_hom, Iso.symm_hom]
    rw [reassoc_of% hai]
    change a₀.inv ≫ F.map (SheafOfModules.ιFree i) ≫
        e.hom.app _ ≫ (b K).hom = _
    rw [e.hom.naturality_assoc, hb]
    simp only [Category.assoc]
    rfl
  let φ := (b I).inv ≫ f ≫ (b J).hom
  have hc := scalar_naturality c₀.hom (c I).hom (c J).hom (hι I) (hι J) φ
  have hconj : (c I).hom ≫ φ ≫ (c J).inv = φ := by
    rw [← Category.assoc, hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simpa [c, φ] using hconj

private lemma restrict_free_inclusion {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsOpenImmersion j] {I : Type u} (i : I) :
    (restrictFunctor j).map (SheafOfModules.ιFree i) ≫ (restrictFreeIso j I).hom =
      ((restrictFunctorIsoPullback j).app (Modules.unit X)).hom ≫
        (pullbackObjUnitIso j).hom ≫ SheafOfModules.ιFree i := by
  dsimp only [restrictFreeIso, Iso.trans_hom]
  change (restrictFunctor j).map (SheafOfModules.ιFree i) ≫
    (restrictFunctorIsoPullback j).hom.app _ ≫ (pullbackFreeIso j I).hom = _
  rw [(restrictFunctorIsoPullback j).hom.naturality_assoc,
    pullback_map_ιFree_pullbackFreeIso_hom]
  rfl

-- Only naturality of the comparison is needed; no composition-coherence computation.
private lemma comparison_normalized {Y : Scheme.{u}} (y : Y)
    (V : Y.Opens) (hyV : y ∈ V) (U : Y.Opens) (hUV : U ≤ V) (hyU : y ∈ U)
    (e : restrictFunctor (Y.homOfLE hUV) ⋙ pullback (U.fromSpecStalkOfMem y hyU) ≅
      pullback (V.fromSpecStalkOfMem y hyV))
    {I J : Type u} [Finite J]
    (f : (pullback (V.fromSpecStalkOfMem y hyV)).obj (SheafOfModules.free I) ⟶
      (pullback (V.fromSpecStalkOfMem y hyV)).obj (SheafOfModules.free J)) :
    let S := pullback (U.fromSpecStalkOfMem y hyU)
    let a (K : Type u) := S.mapIso (restrictFreeIso (Y.homOfLE hUV) K) ≪≫
      pullbackFreeIso (U.fromSpecStalkOfMem y hyU) K
    (a I).inv ≫ (e.app _).hom ≫ f ≫ (e.app _).inv ≫ (a J).hom =
      (pullbackFreeIso (V.fromSpecStalkOfMem y hyV) I).inv ≫ f ≫
        (pullbackFreeIso (V.fromSpecStalkOfMem y hyV) J).hom := by
  dsimp only
  apply free_conjugate_comparison _ _ e
    ((pullback (U.fromSpecStalkOfMem y hyU)).mapIso
      ((restrictFunctorIsoPullback (Y.homOfLE hUV)).app (Modules.unit V.toScheme) ≪≫
        pullbackObjUnitIso (Y.homOfLE hUV)) ≪≫
      pullbackObjUnitIso (U.fromSpecStalkOfMem y hyU))
    (pullbackObjUnitIso (V.fromSpecStalkOfMem y hyV))
  · intro K i
    simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
      ← Functor.map_comp_assoc]
    rw [restrict_free_inclusion]
    simp only [Functor.map_comp, Category.assoc,
      pullback_map_ιFree_pullbackFreeIso_hom]
  · intro K i
    exact pullback_map_ιFree_pullbackFreeIso_hom _ i

private lemma finite_scalar_lift {Y : Scheme.{u}} {κ : Type v} [Finite κ]
    (y : Y) (V : Y.Opens) (hyV : y ∈ V)
    (a : κ → Y.presheaf.stalk y) :
    ∃ (U : Y.Opens) (_ : U ≤ V) (hyU : y ∈ U) (b : κ → Γ(Y, U)),
      ∀ k, Y.presheaf.germ U y hyU (b k) = a k := by
  classical
  let := Fintype.ofFinite κ
  have h : ∀ k, ∃ U ≤ V, ∃ (hyU : y ∈ U) (b : Γ(Y, U)),
      Y.presheaf.germ U y hyU b = a k :=
    fun k ↦ Y.presheaf.exists_le_germ_eq (a k) hyV
  choose W hWV hyW b hb using h
  let U := V ⊓ ⨅ k, W k
  have hUW (k : κ) : U ≤ W k := inf_le_right.trans (iInf_le _ k)
  have hyU : y ∈ U := ⟨hyV, by
    change y ∈ ((⨅ k, W k : Y.Opens) : Set Y)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hyW⟩
  refine ⟨U, inf_le_left, hyU,
    fun k ↦ Y.presheaf.map (homOfLE (hUW k)).op (b k), ?_⟩
  intro k
  exact (Y.presheaf.germ_res_apply (homOfLE (hUW k)) y hyU (b k)).trans (hb k)

private lemma stalk_appTop_eq_germ {Y : Scheme.{u}}
    (y : Y) (U : Y.Opens) (hyU : y ∈ U) :
    (U.fromSpecStalkOfMem y hyU).appTop ≫ (ΓSpecIso (Y.presheaf.stalk y)).hom =
      U.topIso.hom ≫ Y.presheaf.germ U y hyU := by
  have h := congrArg (fun f ↦ f.appTop ≫ (ΓSpecIso (Y.presheaf.stalk y)).hom)
    (U.fromSpecStalkOfMem_toSpecΓ y hyU)
  simp only [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
    Category.assoc, ΓSpecIso_naturality] at h
  exact (cancel_epi ((ΓSpecIso Γ(Y, U)).hom ≫ U.topIso.inv)).mp (by simpa using h)

/-- A finite family of maps between standard finite free sheaves lifts to one open.

Source: lemma-coherent-base-change-invertible-sheaves--3, extension of the finite calculation near a
point; lem-pc-finite-free-reverse-components-lift, proof steps 2 and 3.

Proof: PullbackFreeIso identifies the source and target of each f q with
standard free sheaves over Spec O_{Y,y}. Express f q as a matrix in these
standard bases, using freeMatrix. Its entries are global functions on
Spec O_{Y,y}, hence elements of O_{Y,y}, via the global-sections isomorphism
for Spec. For each entry choose an open neighbourhood of y inside V and a
section representing its germ. There are finitely many entries, since the
index type and every rank are finite. Take the intersection U of these opens
and restrict the representative sections to U. Use the restricted standard
bases, identified by restrictFreeIso, to define g q by the matrix of these
sections. The theorem freeMatrix_pullback and the germ equalities identify
the normalized stalk pullbacks of these maps with the normalized given maps.
To compare with the specified natural isomorphism e, use naturality on the
standard free inclusions. After normalization by restrictFreeIso and
pullbackFreeIso, every component of e acts on each summand by the same
endomorphism of the unit sheaf. Such endomorphisms commute, since they act
by multiplication by a global function. This common scalar therefore
commutes with every finite matrix, so conjugation by e gives the same
normalized map. Cancel the free isomorphisms to obtain the required equalities.
Empty index types and zero ranks have no coefficients; take U=V
when the coefficient list is empty. There is no change of arbitrary bases,
complex, boundedness condition, or reverse-degree support in this lemma.
(blueprint: lem-pc-finite-free-stalk-finite-matrix-lift) -/
theorem exists_finite_free_matrices_of_stalk_local
    {Y : Scheme.{u}} {ι : Type v} [Finite ι]
    (y : Y) (V : Y.Opens) (hyV : y ∈ V)
    (r s : ι → ℕ)
    (f : ∀ q,
      (pullback (V.fromSpecStalkOfMem y hyV)).obj
          (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin (r q)))) ⟶
      (pullback (V.fromSpecStalkOfMem y hyV)).obj
          (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin (s q))))) :
    ∃ (U : Y.Opens) (hUV : U ≤ V) (hyU : y ∈ U),
      let R := restrictFunctor (Y.homOfLE hUV)
      let S := pullback (U.fromSpecStalkOfMem y hyU)
      let e := stalkRestrictionWithinIso y V hyV U hUV hyU
      ∃ (g : ∀ q,
        R.obj (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin (r q)))) ⟶
        R.obj (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin (s q))))),
        ∀ q, S.map (g q) =
          (e.app (SheafOfModules.free (R := V.toScheme.ringCatSheaf)
            (ULift.{u} (Fin (r q))))).hom ≫ f q ≫
          (e.app (SheafOfModules.free (R := V.toScheme.ringCatSheaf)
            (ULift.{u} (Fin (s q))))).inv := by
  classical
  let t := V.fromSpecStalkOfMem y hyV
  let φ (q : ι) := (pullbackFreeIso t (ULift.{u} (Fin (r q)))).inv ≫ f q ≫
    (pullbackFreeIso t (ULift.{u} (Fin (s q)))).hom
  -- The dependent sum lists every coefficient, including varying ranks.
  let κ := Σ q : ι, ULift.{u} (Fin (s q)) × ULift.{u} (Fin (r q))
  let a : κ → Y.presheaf.stalk y := fun k ↦
    (ΓSpecIso (Y.presheaf.stalk y)).hom (freeMatrix (φ k.1) k.2.1 k.2.2)
  obtain ⟨U, hUV, hyU, b, hb⟩ := finite_scalar_lift y V hyV a
  let S := pullback (U.fromSpecStalkOfMem y hyU)
  let A (q : ι) : Matrix (ULift.{u} (Fin (s q))) (ULift.{u} (Fin (r q)))
      Γ(U.toScheme, ⊤) := fun j i ↦ U.topIso.inv (b ⟨q, j, i⟩)
  let h (q : ι) := matrixHom (A q)
  let g (q : ι) := (restrictFreeIso (Y.homOfLE hUV) (ULift.{u} (Fin (r q)))).hom ≫
    h q ≫ (restrictFreeIso (Y.homOfLE hUV) (ULift.{u} (Fin (s q)))).inv
  refine ⟨U, hUV, hyU, g, ?_⟩
  intro q
  let c (K : Type u) := S.mapIso (restrictFreeIso (Y.homOfLE hUV) K) ≪≫
    pullbackFreeIso (U.fromSpecStalkOfMem y hyU) K
  apply (cancel_epi (c (ULift.{u} (Fin (r q)))).inv).mp
  apply (cancel_mono (c (ULift.{u} (Fin (s q)))).hom).mp
  have hn : (pullbackFreeIso (U.fromSpecStalkOfMem y hyU)
        (ULift.{u} (Fin (r q)))).inv ≫ S.map (h q) ≫
      (pullbackFreeIso (U.fromSpecStalkOfMem y hyU)
        (ULift.{u} (Fin (s q)))).hom = φ q := by
    apply freeMatrix_injective
    rw [freeMatrix_pullback, freeMatrix_matrixHom]
    ext j i
    apply (ΓSpecIso (Y.presheaf.stalk y)).commRingCatIsoToRingEquiv.injective
    change (ΓSpecIso (Y.presheaf.stalk y)).hom
      ((U.fromSpecStalkOfMem y hyU).appTop (U.topIso.inv (b ⟨q, j, i⟩))) = _
    have hg := ConcreteCategory.congr_hom (stalk_appTop_eq_germ y U hyU)
      (U.topIso.inv (b ⟨q, j, i⟩))
    simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at hg
    exact hg.trans (hb ⟨q, j, i⟩)
  have he := comparison_normalized y V hyV U hUV hyU
    (stalkRestrictionWithinIso y V hyV U hUV hyU) (f q)
  change (c (ULift.{u} (Fin (r q)))).inv ≫ S.map (g q) ≫
      (c (ULift.{u} (Fin (s q)))).hom = _
  rw [show (c (ULift.{u} (Fin (r q)))).inv ≫ S.map (g q) ≫
      (c (ULift.{u} (Fin (s q)))).hom =
      (pullbackFreeIso (U.fromSpecStalkOfMem y hyU)
        (ULift.{u} (Fin (r q)))).inv ≫ S.map (h q) ≫
      (pullbackFreeIso (U.fromSpecStalkOfMem y hyU)
        (ULift.{u} (Fin (s q)))).hom by
    simp [c, g, Functor.map_comp, Category.assoc]]
  exact hn.trans he.symm

end AlgebraicGeometry.Scheme.Modules
