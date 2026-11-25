/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.LinearAlgebra.Quotient.Basic
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineOpenSectionsAdic
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Algebra.Category.ModuleCat.AdicTowerCompletedScalarLimit
import WeilConjectures.Algebra.Category.ModuleCat.AdicTowerFiniteLimit
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Affine comparison of formal kernel images with module quotients

Source: Stacks Project, Lemma 087X, affine description of K'_(l,m), using Lemma 087W.
(blueprint: new-formal-affine-kernel-image-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Build the completed modules from the section towers. The completion action is
coordinatewise, the finite-limit theorem supplies the projection kernels, and the
map of limits induced by alpha is completion-linear by checking every projection. -/
private theorem completed_projections
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (F H : CoherentFormalModule X I) (α : F ⟶ H) (U : X.affineOpens) :
    let A := Γ(X, U.1)
    let R := AdicCompletion (I.ideal U) A
    let J := (I.ideal U).map (algebraMap A R)
    ∃ (M N : ModuleCat.{u} R) (f : M ⟶ N),
      Module.Finite R M ∧ Module.Finite R N ∧
      ∃ (p : ∀ n : ℕ, M →+ Γ(F.obj.obj (op n), U.1))
        (q : ∀ n : ℕ, N →+ Γ(H.obj.obj (op n), U.1)),
        (∀ n : ℕ, Function.Surjective (p n)) ∧
        (∀ (n : ℕ) (x : M), p n x = 0 ↔
          x ∈ J ^ (n + 1) • (⊤ : Submodule R M)) ∧
        (∀ (n : ℕ) (y : N), q n y = 0 ↔
          y ∈ J ^ (n + 1) • (⊤ : Submodule R N)) ∧
        (∀ (n : ℕ) (x : M), q n (f x) = (α.hom.app (op n)).app U.1 (p n x)) ∧
        (∀ (l m : ℕ) (h : m ≤ l) (x : M),
          p m x = (F.obj.map (homOfLE h).op).app U.1 (p l x)) := by
  classical
  let A := Γ(X, U.1)
  let K := I.ideal U
  let R := AdicCompletion K A
  let S := ModuleCat.restrictScalars (algebraMap A R)
  let G := SheafOfModules.evaluation X.ringCatSheaf (op U.1)
  let TF := F.obj ⋙ G
  let TH := H.obj ⋙ G
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian U
  have hF := coherentFormalModule_affine_open_sections_adic X I F U
  have hH := coherentFormalModule_affine_open_sections_adic X I H U
  obtain ⟨M, eM, hsM⟩ := ModuleCat.adicTower_completedScalarLimit A K TF hF.2.1
  obtain ⟨N, eN, hsN⟩ := ModuleCat.adicTower_completedScalarLimit A K TH hH.2.1
  have hM := ModuleCat.adicTower_finiteLimit A K TF hF.1 hF.2.1 hF.2.2 M eM hsM
  have hN := ModuleCat.adicTower_finiteLimit A K TH hH.1 hH.2.1 hH.2.2 N eN hsN
  let p (n : ℕ) : S.obj M ⟶ TF.obj (op n) := eM.hom ≫ limit.π TF (op n)
  let q (n : ℕ) : S.obj N ⟶ TH.obj (op n) := eN.hom ≫ limit.π TH (op n)
  let t : TF ⟶ TH := Functor.whiskerRight α.hom G
  let g : S.obj M ⟶ S.obj N := eM.hom ≫ lim.map t ≫ eN.inv
  have hg (n : ℕ) : g ≫ q n = p n ≫ t.app (op n) := by
    simp [g, p, q, Category.assoc]
  have hg_apply (n : ℕ) (x : M) : q n (g x) = t.app (op n) (p n x) :=
    congrArg (fun k ↦ k x) (hg n)
  have hlinear (r : R) (x : M) : g (r • x) = r • g x := by
    apply (ModuleCat.mono_iff_injective eN.hom).mp inferInstance
    apply Concrete.limit_ext TH
    intro j
    obtain ⟨n⟩ := j
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ K (n + 1) r)
    have hsp := hsM n r a x ha.symm
    have hsq := hsN n r a (g x) ha.symm
    change q n (g (r • x)) = q n (r • g x)
    change p n (r • x) = a • p n x at hsp
    change q n (r • g x) = a • q n (g x) at hsq
    rw [hsq, hg_apply, hsp, map_smul, hg_apply]
  let f : M ⟶ N := ModuleCat.ofHom
    { toFun := g
      map_add' := map_add g.hom
      map_smul' := hlinear }
  have hkernel (L : ModuleCat.{u} R) (n : ℕ) (x : L) :
      x ∈ K ^ (n + 1) • (⊤ : Submodule A (S.obj L)) ↔
      x ∈ (K.map (algebraMap A R)) ^ (n + 1) • (⊤ : Submodule R L) := by
    let : Module A L := Module.compHom L (algebraMap A R)
    let : IsScalarTower A R L := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    have he : (((K.map (algebraMap A R)) ^ (n + 1) •
        (⊤ : Submodule R L)).restrictScalars A) =
        K ^ (n + 1) • (⊤ : Submodule A L) := by
      rw [← Ideal.map_pow]
      exact Submodule.restrictScalars_map_smul_eq (K ^ (n + 1)) ⊤
    exact (SetLike.ext_iff.mp he x).symm
  refine ⟨M, N, f, hM.1, hN.1,
    (fun n ↦ (p n).hom.toAddMonoidHom), (fun n ↦ (q n).hom.toAddMonoidHom),
    (fun n ↦ (hM.2 n).1), ?_, ?_, ?_, ?_⟩
  · intro n x
    change p n x = 0 ↔ _
    rw [← hkernel M n x]
    exact SetLike.ext_iff.mp (hM.2 n).2 x
  · intro n y
    change q n y = 0 ↔ _
    rw [← hkernel N n y]
    exact SetLike.ext_iff.mp (hN.2 n).2 y
  · intro n x
    exact hg_apply n x
  · intro l m h x
    have hw : p l ≫ TF.map (homOfLE h).op = p m := by
      dsimp only [p]
      rw [Category.assoc, limit.w]
    exact (congrArg (fun k ↦ k x) hw).symm

private theorem app_zero_below_affine {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] (φ : M ⟶ N) (U : X.affineOpens)
    (h : ∀ t : Γ(M, U.1), φ.app U.1 t = 0)
    (W : X.Opens) (hWU : W ≤ U.1) (s : Γ(M, W)) : φ.app W s = 0 := by
  classical
  have local_zero (x : W) : ∃ (V : X.Opens) (hVW : V ≤ W),
      x.1 ∈ V ∧ φ.app V (M.presheaf.map (homOfLE hVW).op s) = 0 := by
    obtain ⟨g, hgW, hxg⟩ := U.2.exists_basicOpen_le ⟨x.1, x.2⟩ (hWU x.2)
    obtain ⟨k, t, ht⟩ := Scheme.Modules.exists_map_eq_pow_smul_of_isAffineOpen
      M U.2 g (M.presheaf.map (homOfLE hgW).op s)
    have hz : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op g) ^ k •
        φ.app (X.basicOpen g) (M.presheaf.map (homOfLE hgW).op s) = 0 := by
      rw [← Scheme.Modules.Hom.app_smul, ← ht, Scheme.Modules.Hom.app_presheaf_map,
        h, map_zero]
    have hu : IsUnit ((X.presheaf.map
        (homOfLE (X.basicOpen_le g)).op g) ^ k) :=
      (X.toRingedSpace.isUnit_res_basicOpen g).pow k
    refine ⟨X.basicOpen g, hgW, hxg, ?_⟩
    calc
      _ = hu.unit⁻¹.1 • ((X.presheaf.map
          (homOfLE (X.basicOpen_le g)).op g) ^ k •
          φ.app (X.basicOpen g) (M.presheaf.map (homOfLE hgW).op s)) := by
        rw [smul_smul, IsUnit.val_inv_mul, one_smul]
      _ = 0 := by rw [hz, smul_zero]
  choose V hVW hxV hz using local_zero
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩ V W
    (fun x ↦ homOfLE (hVW x)) ?_ _ _ ?_
  · intro x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  · intro x
    rw [map_zero, ← Scheme.Modules.Hom.app_presheaf_map]
    exact hz x

private theorem mono_range_subset_below_affine {X : Scheme.{u}} {M N P : X.Modules}
    [M.IsQuasicoherent] (i : M ⟶ P) (j : N ⟶ P) [Mono j] (U : X.affineOpens)
    (h : Set.range (i.app U.1) ⊆ Set.range (j.app U.1))
    (W : X.Opens) (hWU : W ≤ U.1) : Set.range (i.app W) ⊆ Set.range (j.app W) := by
  intro s hs
  obtain ⟨t, rfl⟩ := hs
  have hz : (cokernel.π j).app W (i.app W t) = 0 := by
    apply app_zero_below_affine (i ≫ cokernel.π j) U _ W hWU t
    intro a
    obtain ⟨b, hb⟩ := h ⟨a, rfl⟩
    change (cokernel.π j).app U.1 (i.app U.1 a) = 0
    rw [← hb]
    exact congrArg (fun q ↦ q.app U.1 b) (cokernel.condition j)
  obtain ⟨a, ha⟩ := (Set.ext_iff.mp
    (Scheme.Modules.range_map_kernelι W (cokernel.π j)) (i.app W t)).mpr hz
  refine ⟨(inv (Abelian.factorThruImage j)).app W a, ?_⟩
  have hf : inv (Abelian.factorThruImage j) ≫ j = Abelian.image.ι j := by
    calc
      _ = inv (Abelian.factorThruImage j) ≫
          Abelian.factorThruImage j ≫ Abelian.image.ι j :=
        congrArg (fun q ↦ inv (Abelian.factorThruImage j) ≫ q)
          (Abelian.image.fac j).symm
      _ = _ := by rw [IsIso.inv_hom_id_assoc]
  exact (congrArg (fun q ↦ q.app W a) hf).trans ha

private theorem mono_range_eq_below_affine {X : Scheme.{u}} {M N P : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (i : M ⟶ P) (j : N ⟶ P) [Mono i] [Mono j] (U : X.affineOpens) :
    Set.range (i.app U.1) = Set.range (j.app U.1) ↔
      ∀ (W : X.Opens), W ≤ U.1 → Set.range (i.app W) = Set.range (j.app W) := by
  constructor
  · intro h W hWU
    exact Set.Subset.antisymm
      (mono_range_subset_below_affine i j U h.subset W hWU)
      (mono_range_subset_below_affine j i U h.symm.subset W hWU)
  · intro h
    exact h U.1 le_rfl

private theorem quotient_map_eq_iff_additive_image_eq
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    {T : Type u} [AddCommGroup T] (S P Q : Submodule R M) (p : M →+ T)
    (hp : ∀ x : M, p x = 0 ↔ x ∈ S) :
    P.map S.mkQ = Q.map S.mkQ ↔ Set.image p (P : Set M) = Set.image p (Q : Set M) := by
  have hf (x y : M) : p x = p y ↔ S.mkQ x = S.mkQ y := by
    calc
      p x = p y ↔ p (x - y) = 0 := by rw [map_sub, sub_eq_zero]
      _ ↔ x - y ∈ S := hp _
      _ ↔ S.mkQ (x - y) = 0 := (Submodule.Quotient.mk_eq_zero S).symm
      _ ↔ S.mkQ x = S.mkQ y := by rw [map_sub, sub_eq_zero]
  have hle (P Q : Submodule R M) :
      P.map S.mkQ ≤ Q.map S.mkQ ↔ Set.image p (P : Set M) ⊆ Set.image p (Q : Set M) := by
    constructor
    · intro h z hz
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨y, hy, he⟩ := h (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
      exact ⟨y, hy, (hf y x).mpr he⟩
    · intro h z hz
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨y, hy, he⟩ := h ⟨x, hx, rfl⟩
      exact Submodule.mem_map.mpr ⟨y, hy, (hf y x).mp he⟩
  constructor
  · intro h
    exact Set.Subset.antisymm ((hle P Q).mp h.le) ((hle Q P).mp h.ge)
  · intro h
    exact le_antisymm ((hle P Q).mpr h.subset) ((hle Q P).mpr h.symm.subset)

private theorem kernel_transition_range
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (F H : CoherentFormalModule X I) (α : F ⟶ H) (U : X.affineOpens)
    {R : Type u} [CommRing R] (J : Ideal R) (M N : ModuleCat.{u} R) (f : M ⟶ N)
    (p : ∀ n : ℕ, M →+ Γ(F.obj.obj (op n), U.1))
    (q : ∀ n : ℕ, N →+ Γ(H.obj.obj (op n), U.1))
    (hp : ∀ n : ℕ, Function.Surjective (p n))
    (hq : ∀ (n : ℕ) (y : N), q n y = 0 ↔ y ∈ J ^ (n + 1) • (⊤ : Submodule R N))
    (hf : ∀ (n : ℕ) (x : M), q n (f x) = (α.hom.app (op n)).app U.1 (p n x))
    (ht : ∀ (l m : ℕ) (h : m ≤ l) (x : M),
      p m x = (F.obj.map (homOfLE h).op).app U.1 (p l x))
    (l m : ℕ) (h : m ≤ l) :
    Set.image (p m) (((J ^ (l + 1) • (⊤ : Submodule R N)).comap f.hom) : Set M) =
      Set.range ((kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE h).op).app U.1) := by
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hz : (α.hom.app (op l)).app U.1 (p l x) = 0 := by
      rw [← hf]
      exact (hq l (f x)).mpr hx
    obtain ⟨a, ha⟩ := (Set.ext_iff.mp
      (Scheme.Modules.range_map_kernelι U.1 (α.hom.app (op l))) (p l x)).mpr hz
    refine ⟨a, ?_⟩
    change (F.obj.map (homOfLE h).op).app U.1
      ((kernel.ι (α.hom.app (op l))).app U.1 a) = p m x
    change (kernel.ι (α.hom.app (op l))).app U.1 a = p l x at ha
    rw [ha]
    exact (ht l m h x).symm
  · rintro ⟨a, rfl⟩
    obtain ⟨x, hx⟩ := hp l ((kernel.ι (α.hom.app (op l))).app U.1 a)
    refine ⟨x, ?_, ?_⟩
    · apply (hq l (f x)).mp
      rw [hf, hx]
      exact congrArg (fun g ↦ g.app U.1 a) (kernel.condition (α.hom.app (op l)))
    · change p m x = (F.obj.map (homOfLE h).op).app U.1
        ((kernel.ι (α.hom.app (op l))).app U.1 a)
      rw [ht l m h x, hx]

/-- On an affine open, comparison of any two finite-level kernel image subsheaves
is equivalent to comparison of the corresponding quotient submodules of a completed
module. There is no stabilization assertion or Artin--Rees bound in this statement.

Source: Stacks Project, Lemma 087X, description of K'_(l,m) before claim (a),
and Lemma 087W; Schemes, Tags 01IB and 01IC.
(blueprint: new-formal-affine-kernel-image-comparison).

Proof: Restrict F, H and alpha to U and identify U with Spec A for A = Gamma(U,O_X).
Restriction preserves the defining coherent formal object conditions. Apply 087W to
these systems and their morphism to obtain finite completed modules M, N and a linear
map f. Put J = I(U)R in the completed ring R. The level-n projections are surjective
and have kernels J^(n+1)M and J^(n+1)N. Hence sections of ker(alpha_l) lift precisely
to f inverse(J^(l+1)N), and transition to level m sends their lifts to their classes
modulo J^(m+1)M. Affine sections of the abelian image equal the ordinary linear image.
The tilde/global-sections equivalence identifies the image inclusion with the tilde
of this quotient submodule inclusion. Thus equal quotient submodules give equal
subsheaves on U, and consequently equal section ranges on every W contained in U.
Conversely equality of these ranges includes equality at W = U; the affine quotient
identification recovers equality of the two submodules. Restriction of scalars from
R to A preserves equality of underlying submodules. No finiteness or affine assumption
on W is used. On empty U, A and R are zero rings and both sides are the unique zero
submodule; zero and unit ideals give the same quotient computations. -/
theorem coherentFormalModule_affine_kernel_image_comparison
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (F H : CoherentFormalModule X I) (α : F ⟶ H) (U : X.affineOpens) :
    let A := Γ(X, U.1)
    let R := AdicCompletion (I.ideal U) A
    let J := (I.ideal U).map (algebraMap A R)
    ∃ (M N : ModuleCat.{u} R) (f : M ⟶ N),
      Module.Finite R M ∧ Module.Finite R N ∧
      ∀ (l k m : ℕ) (hl : m ≤ l) (hk : m ≤ k),
        (((J ^ (l + 1) • (⊤ : Submodule R N)).comap f.hom).map
            (J ^ (m + 1) • (⊤ : Submodule R M)).mkQ =
          ((J ^ (k + 1) • (⊤ : Submodule R N)).comap f.hom).map
            (J ^ (m + 1) • (⊤ : Submodule R M)).mkQ) ↔
        ∀ (W : X.Opens), W ≤ U.1 →
          Set.range ((Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE hl).op)).app W) =
          Set.range ((Abelian.image.ι (kernel.ι (α.hom.app (op k)) ≫
            F.obj.map (homOfLE hk).op)).app W) := by
  obtain ⟨M, N, f, hM, hN, p, q, hp, hpk, hqk, hf, ht⟩ :=
    completed_projections I F H α U
  refine ⟨M, N, f, hM, hN, ?_⟩
  intro l k m hl hk
  let J := (I.ideal U).map
    (algebraMap Γ(X, U.1) (AdicCompletion (I.ideal U) Γ(X, U.1)))
  let a := kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE hl).op
  let b := kernel.ι (α.hom.app (op k)) ≫ F.obj.map (homOfLE hk).op
  have qc (n : ℕ) : (F.obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
      (F.property.1 n)).1
  have qh (n : ℕ) : (H.obj.obj (op n)).IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
      (H.property.1 n)).1
  have := qc l
  have := qc k
  have := qc m
  have := qh l
  have := qh k
  have := Scheme.Modules.isQuasicoherent_kernel (α.hom.app (op l))
  have := Scheme.Modules.isQuasicoherent_kernel (α.hom.app (op k))
  have ha := Scheme.Modules.quasiCoherent_cokernel_image a
  have hb := Scheme.Modules.quasiCoherent_cokernel_image b
  have := ha.2.2.2.2.2.2.2.1
  have := hb.2.2.2.2.2.2.2.1
  rw [quotient_map_eq_iff_additive_image_eq _ _ _ (p m) (hpk m),
    kernel_transition_range I F H α U J M N f p q hp hqk hf ht l m hl,
    kernel_transition_range I F H α U J M N f p q hp hqk hf ht k m hk,
    ← (ha.2.2.2.2.2.2.2.2 U).1, ← (hb.2.2.2.2.2.2.2.2 U).1]
  exact mono_range_eq_below_affine (Abelian.image.ι a) (Abelian.image.ι b) U

end AlgebraicGeometry
