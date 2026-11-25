/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.AlgebraicGeometry.TensorFreeFrameCoordinates
import WeilConjectures.AlgebraicGeometry.EtaleTensorHomEvaluationNaturality

/-!
# Fixed points of a Frobenius-linear map in a free frame

For a quasi-coherent module `E` on `S` with a finite free frame and a Frobenius-linear
endomorphism `F` of its étale sheaf of sections, the sections over an étale `U` of the
abelian kernel of `F - 1` are the solutions `x : Fin n → Γ(U, ⊤)` of
`x_i = ∑_j a_ij x_j ^ p`, naturally in `U`.

Source: Stacks Project, Tag 0GKU, proof of lemma-frobenius-linear-on-vb.
(blueprint: lem-fd-frobenius-linear-free-kernel-stratification).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Sections of a difference of morphisms of abelian sheaves. -/
private theorem sheaf_sub_hom_app_apply {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {P Q : Sheaf J AddCommGrpCat.{u}} (f g : P ⟶ Q) (U : Cᵒᵖ)
    (m : P.obj.obj U) : (f - g).hom.app U m = f.hom.app U m - g.hom.app U m :=
  rfl

attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj
attribute [local instance 2000]
  Modules.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

/-- On sections, the kernel inclusion of abelian sheaves is the kernel inclusion of the map of
section groups, up to the comparison isomorphism. -/
private theorem sheaf_kernel_ι_app_eq {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {P Q : Sheaf J AddCommGrpCat.{u}} (φ : P ⟶ Q) (U : Cᵒᵖ) :
    (kernel.ι φ).hom.app U =
      (PreservesKernel.iso
        (sheafToPresheaf J AddCommGrpCat.{u} ⋙ (CategoryTheory.evaluation _ _).obj U)
        φ).hom ≫ kernel.ι
          ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
            (CategoryTheory.evaluation _ _).obj U).map φ) := by
  rw [← PreservesKernel.iso_inv_ι, Iso.hom_inv_id_assoc]
  rfl

/-- Sections of the kernel of a map of abelian sheaves inject into the sections of the source. -/
private theorem sheaf_kernel_ι_app_injective {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {P Q : Sheaf J AddCommGrpCat.{u}} (φ : P ⟶ Q) (U : Cᵒᵖ) :
    Function.Injective ((kernel.ι φ).hom.app U) := by
  rw [← AddCommGrpCat.mono_iff_injective, sheaf_kernel_ι_app_eq]
  infer_instance

/-- Every element annihilated by a map of abelian groups lifts to its categorical kernel. -/
private theorem addCommGrpCat_exists_kernel_ι_eq {A B : AddCommGrpCat.{u}} (f : A ⟶ B) (m : A)
    (hm : f m = 0) : ∃ s, kernel.ι f s = m :=
  ⟨(AddCommGrpCat.kernelIsoKer f).inv ⟨m, hm⟩, by
    rw [← ConcreteCategory.comp_apply, AddCommGrpCat.kernelIsoKer_inv_comp_ι]
    rfl⟩

/-- Every section annihilated by `φ` comes from the kernel sheaf. -/
private theorem sheaf_kernel_ι_app_surjective {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {P Q : Sheaf J AddCommGrpCat.{u}} (φ : P ⟶ Q) (U : Cᵒᵖ)
    (m : P.obj.obj U) (hm : φ.hom.app U m = 0) :
    ∃ s, (kernel.ι φ).hom.app U s = m := by
  obtain ⟨s, hs⟩ := addCommGrpCat_exists_kernel_ι_eq
    ((sheafToPresheaf J AddCommGrpCat.{u} ⋙ (CategoryTheory.evaluation _ _).obj U).map φ) m hm
  refine ⟨(PreservesKernel.iso
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙ (CategoryTheory.evaluation _ _).obj U) φ).inv s,
    ?_⟩
  rw [sheaf_kernel_ι_app_eq, ConcreteCategory.comp_apply]
  exact (congrArg (fun y ↦ kernel.ι ((sheafToPresheaf J AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation _ _).obj U).map φ) y) (Iso.inv_hom_id_apply _ s)).trans hs

/-- The étale object given by the identity of `S`; it is terminal in `S.Etale`. -/
private noncomputable abbrev etaleSelf (S : Scheme.{u}) : S.Etale := Scheme.Etale.mk (𝟙 S)

/-- The structure map of an étale object, viewed as a morphism to `etaleSelf S`. -/
private noncomputable abbrev toEtaleSelf {S : Scheme.{u}} (U : S.Etale) : U ⟶ etaleSelf S :=
  MorphismProperty.Over.homMk U.hom (Category.comp_id _)

/-- Any morphism to `etaleSelf S` is the structure morphism. -/
private theorem eq_toEtaleSelf {S : Scheme.{u}} {U : S.Etale} (g : U ⟶ etaleSelf S) :
    g = toEtaleSelf U := by
  apply MorphismProperty.Over.Hom.ext
  exact (Category.comp_id _).symm.trans g.w

/-- Expansion of an element in the basis given by a linear equivalence with `Fin n → R`. -/
private theorem sum_coord_smul_symm_single
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    (n : ℕ) (e : M ≃ₗ[R] (Fin n → R)) (m : M) :
    ∑ j, (e m j) • e.symm (Pi.single j 1) = m := by
  classical
  apply e.injective
  simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

/-- A Frobenius-semilinear additive map in coordinates: its value is the Frobenius twist of
the coordinates, multiplied by the coordinates of the values on the basis vectors. -/
private theorem frobenius_expansion
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    (n p : ℕ) (e : M ≃ₗ[R] (Fin n → R)) (f : M →+ M)
    (hf : ∀ (c : R) (m : M), f (c • m) = c ^ p • f m) (m : M) (i : Fin n) :
    e (f m) i = ∑ j, e (f (e.symm (Pi.single j 1))) i * (e m j) ^ p := by
  conv_lhs => rw [← sum_coord_smul_symm_single n e m, map_sum, map_sum]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hf, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- A restriction map of global sections compatible with the scalar actions along `f` is
semilinear for the module structures. -/
private theorem semilinear_of_smul_comp {X Y : Scheme.{u}} {M : X.Modules} {N : Y.Modules}
    (f : Y ⟶ X) (ρ : Γ(M, ⊤) ⟶ Γ(N, ⊤))
    (h : ∀ c, (M.smul c).asHom ≫ ρ = ρ ≫ (N.smul (f.appTop c)).asHom) (c : Γ(X, ⊤)) (x : Γ(M, ⊤)) :
    ρ (c • x) = f.appTop c • ρ x := by
  rw [← Modules.smul_apply, ← Modules.smul_apply, ← ConcreteCategory.comp_apply, h,
    ConcreteCategory.comp_apply]

/-- Coordinates which are natural for restriction from the terminal étale object are natural
for every restriction. The restriction maps are kept abstract, which keeps the kernel from
unfolding the tensor-pullback restriction maps. -/
private theorem coord_restriction_natural_aux {S : Scheme.{u}} (E : S.Modules) (n : ℕ)
    (ρ : ∀ {U W : S.Etale}, (W ⟶ U) → (Γ((Modules.tensorPullback U.hom).obj E, ⊤) ⟶
      Γ((Modules.tensorPullback W.hom).obj E, ⊤)))
    (hcomp : ∀ {U W W' : S.Etale} (h : W' ⟶ W) (g : W ⟶ U), ρ (h ≫ g) = ρ g ≫ ρ h)
    (hsmul : ∀ {U W : S.Etale} (g : W ⟶ U) (c : Γ(U.left, ⊤)),
      (((Modules.tensorPullback U.hom).obj E).smul c).asHom ≫ ρ g =
        ρ g ≫ (((Modules.tensorPullback W.hom).obj E).smul (g.left.appTop c)).asHom)
    (e : ∀ (W : S.Etale), (W ⟶ etaleSelf S) →
      Γ((Modules.tensorPullback W.hom).obj E, ⊤) ≃ₗ[Γ(W.left, ⊤)]
        (Fin n → Γ(W.left, ⊤)))
    (henat : ∀ (W : S.Etale) (h : W ⟶ etaleSelf S)
      (m : Γ((Modules.tensorPullback (etaleSelf S).hom).obj E, ⊤)) (i : Fin n),
      e W h (ρ h m) i = h.left.appTop (e (etaleSelf S) (𝟙 _) m i))
    (U W : S.Etale) (g : W ⟶ U) (m : Γ((Modules.tensorPullback U.hom).obj E, ⊤)) (i : Fin n) :
    e W (toEtaleSelf W) (ρ g m) i = g.left.appTop (e U (toEtaleSelf U) m i) := by
  classical
  let v : Fin n → Γ((Modules.tensorPullback (etaleSelf S).hom).obj E, ⊤) :=
    fun j ↦ (e (etaleSelf S) (𝟙 _)).symm (Pi.single j 1)
  have hw (A : S.Etale) (j : Fin n) :
      ρ (toEtaleSelf A) (v j) = (e A (toEtaleSelf A)).symm (Pi.single j 1) := by
    apply (e A (toEtaleSelf A)).injective
    funext k
    rw [henat]
    simp only [v, LinearEquiv.apply_symm_apply, Pi.single_apply]
    split_ifs <;> simp
  have hc (j : Fin n) : ρ g ((e U (toEtaleSelf U)).symm (Pi.single j 1)) =
      (e W (toEtaleSelf W)).symm (Pi.single j 1) := by
    rw [← hw, ← hw, ← ConcreteCategory.comp_apply, ← hcomp,
      eq_toEtaleSelf (g ≫ toEtaleSelf U)]
  conv_lhs => rw [← sum_coord_smul_symm_single n (e U (toEtaleSelf U)) m, map_sum]
  simp only [semilinear_of_smul_comp g.left (ρ g) (hsmul g), hc, map_sum, map_smul,
    LinearEquiv.apply_symm_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- `coord_restriction_natural_aux` for restriction maps typed as maps of sections of the
étale tensor-section sheaf. -/
private theorem coord_restriction_natural {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
    (n : ℕ)
    (ρ : ∀ {U W : S.Etale}, (W ⟶ U) →
      ((Modules.etaleTensorSectionsSheaf E).obj.obj (op U) ⟶
        (Modules.etaleTensorSectionsSheaf E).obj.obj (op W)))
    (hcomp : ∀ {U W W' : S.Etale} (h : W' ⟶ W) (g : W ⟶ U), ρ (h ≫ g) = ρ g ≫ ρ h)
    (hsmul : ∀ {U W : S.Etale} (g : W ⟶ U) (c : Γ(U.left, ⊤)),
      (((Modules.tensorPullback U.hom).obj E).smul c).asHom ≫ ρ g =
        ρ g ≫ (((Modules.tensorPullback W.hom).obj E).smul (g.left.appTop c)).asHom)
    (e : ∀ (W : S.Etale), (W ⟶ etaleSelf S) →
      Γ((Modules.tensorPullback W.hom).obj E, ⊤) ≃ₗ[Γ(W.left, ⊤)]
        (Fin n → Γ(W.left, ⊤)))
    (henat : ∀ (W : S.Etale) (h : W ⟶ etaleSelf S)
      (m : Γ((Modules.tensorPullback (etaleSelf S).hom).obj E, ⊤)) (i : Fin n),
      e W h (ρ h m) i = h.left.appTop (e (etaleSelf S) (𝟙 _) m i))
    (U W : S.Etale) (g : W ⟶ U) (m : Γ((Modules.tensorPullback U.hom).obj E, ⊤)) (i : Fin n) :
    e W (toEtaleSelf W) (ρ g m) i = g.left.appTop (e U (toEtaleSelf U) m i) :=
  coord_restriction_natural_aux E n (fun g ↦ ρ g) hcomp hsmul e henat U W g m i

/-- Natural linear coordinates on all tensor sections, for an arbitrary restriction map. -/
private theorem exists_etale_free_frame_coordinates
    (S : Scheme.{u}) (E : S.Modules) [E.IsQuasicoherent] (n : ℕ)
    (α : E ≅ SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))) :
    ∃ (e : ∀ (W : S.Etale),
        Γ((Modules.tensorPullback W.hom).obj E, ⊤) ≃ₗ[Γ(W.left, ⊤)]
          (Fin n → Γ(W.left, ⊤))),
      ∀ (U W : S.Etale) (g : W ⟶ U)
        (m : Γ((Modules.tensorPullback U.hom).obj E, ⊤)) (i : Fin n),
        e W ((Modules.etaleTensorSectionsSheaf E).obj.map g.op m) i =
          g.left.appTop (e U m i) := by
  let α₀ : (Modules.tensorPullback (etaleSelf S).hom).obj E ≅
      SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)) :=
    (Modules.tensorSectionsPullbackComparison (𝟙 S)).app E ≪≫
      (Scheme.Modules.pullbackId S).app E ≪≫ α
  obtain ⟨e, henat⟩ := exists_natural_tensor_free_frame_coordinates S E (etaleSelf S) n α₀
  exact ⟨fun W ↦ e W (toEtaleSelf W), coord_restriction_natural E n
    (fun g ↦ (Modules.etaleTensorSectionsSheaf E).obj.map g.op)
    (fun h g ↦ (Modules.etaleTensorSectionsSheaf E).obj.map_comp g.op h.op)
    (fun g c ↦ Modules.etaleTensorSectionsRestriction_smul E g c) e henat⟩

/-- The Frobenius matrix: in natural coordinates, a Frobenius-semilinear endomorphism of the
étale tensor-section sheaf is given by a matrix with entries in `Γ(S, ⊤)`. The restriction maps
and the components of the endomorphism are kept abstract for the kernel. -/
private theorem exists_frobenius_matrix_aux {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
    (p n : ℕ)
    (ρ : ∀ {U W : S.Etale}, (W ⟶ U) →
      ((Modules.etaleTensorSectionsSheaf E).obj.obj (op U) ⟶
        (Modules.etaleTensorSectionsSheaf E).obj.obj (op W)))
    (Fapp : ∀ U : S.Etale, (Modules.etaleTensorSectionsSheaf E).obj.obj (op U) ⟶
      (Modules.etaleTensorSectionsSheaf E).obj.obj (op U))
    (hFnat : ∀ {U W : S.Etale} (g : W ⟶ U), ρ g ≫ Fapp W = Fapp U ≫ ρ g)
    (hF : ∀ (U : S.Etale) (a : Γ(U.left, ⊤))
      (e : Γ((Modules.tensorPullback U.hom).obj E, ⊤)),
      Fapp U ((((Modules.tensorPullback U.hom).obj E).smul a).asHom.hom e) =
        (((Modules.tensorPullback U.hom).obj E).smul (a ^ p)).asHom.hom (Fapp U e))
    (e : ∀ (W : S.Etale),
      Γ((Modules.tensorPullback W.hom).obj E, ⊤) ≃ₗ[Γ(W.left, ⊤)]
        (Fin n → Γ(W.left, ⊤)))
    (hnat : ∀ (U W : S.Etale) (g : W ⟶ U)
      (m : Γ((Modules.tensorPullback U.hom).obj E, ⊤)) (i : Fin n),
      e W (ρ g m) i = g.left.appTop (e U m i)) :
    ∃ a : Fin n → Fin n → Γ(S, ⊤), ∀ (U : S.Etale)
      (m : Γ((Modules.tensorPullback U.hom).obj E, ⊤)) (i : Fin n),
      e U (Fapp U m) i =
        ∑ j, (show Γ(U.left, ⊤) from U.hom.appTop (a i j)) * (e U m j) ^ p := by
  classical
  let v : Fin n → Γ((Modules.tensorPullback (etaleSelf S).hom).obj E, ⊤) :=
    fun j ↦ (e (etaleSelf S)).symm (Pi.single j 1)
  refine ⟨fun i j ↦ e (etaleSelf S) (Fapp (etaleSelf S) (v j)) i, ?_⟩
  intro U m i
  have hv (j : Fin n) : ρ (toEtaleSelf U) (v j) = (e U).symm (Pi.single j 1) := by
    apply (e U).injective
    funext k
    rw [hnat]
    simp only [v, LinearEquiv.apply_symm_apply, Pi.single_apply]
    split_ifs <;> simp
  let FU : Γ((Modules.tensorPullback U.hom).obj E, ⊤) →+
      Γ((Modules.tensorPullback U.hom).obj E, ⊤) := (Fapp U).hom
  have hs (c : Γ(U.left, ⊤)) (x : Γ((Modules.tensorPullback U.hom).obj E, ⊤)) :
      FU (c • x) = c ^ p • FU x := by
    rw [← Modules.smul_apply, ← Modules.smul_apply]
    exact hF U c x
  have h1 (x : (Modules.etaleTensorSectionsSheaf E).obj.obj (op (etaleSelf S))) :
      Fapp U (ρ (toEtaleSelf U) x) =
      ρ (toEtaleSelf U) (Fapp (etaleSelf S) x) := by
    rw [← ConcreteCategory.comp_apply, hFnat, ConcreteCategory.comp_apply]
  refine (frobenius_expansion n p (e U) FU hs m i).trans (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [← hv]
  exact congrArg (· * _) ((congrArg (fun x ↦ e U x i) (h1 (v j))).trans (hnat _ _ _ _ _))

/-- Assembly: an injective natural map from `K` onto the fixed points of `Fapp`, together with
natural coordinates in which `Fapp` is a Frobenius matrix, identifies the sections of `K` with
the solutions of the Frobenius fixed-point equations, naturally. All maps are abstract. -/
private theorem exists_kernel_coordinates_aux {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] (p n : ℕ) (K : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
    (ι : ∀ U : S.Etale, K.obj.obj (op U) ⟶ (Modules.etaleTensorSectionsSheaf E).obj.obj (op U))
    (ρ : ∀ {U W : S.Etale}, (W ⟶ U) →
      ((Modules.etaleTensorSectionsSheaf E).obj.obj (op U) ⟶
        (Modules.etaleTensorSectionsSheaf E).obj.obj (op W)))
    (hιnat : ∀ {U W : S.Etale} (g : W ⟶ U), K.obj.map g.op ≫ ι W = ι U ≫ ρ g)
    (Fapp : ∀ U : S.Etale, (Modules.etaleTensorSectionsSheaf E).obj.obj (op U) ⟶
      (Modules.etaleTensorSectionsSheaf E).obj.obj (op U))
    (hinj : ∀ U : S.Etale, Function.Injective (ι U))
    (hfix : ∀ (U : S.Etale) (s : K.obj.obj (op U)), Fapp U (ι U s) = ι U s)
    (hsurj : ∀ (U : S.Etale) (m : (Modules.etaleTensorSectionsSheaf E).obj.obj (op U)),
      Fapp U m = m → ∃ s, ι U s = m)
    (e : ∀ (W : S.Etale),
      Γ((Modules.tensorPullback W.hom).obj E, ⊤) ≃ₗ[Γ(W.left, ⊤)]
        (Fin n → Γ(W.left, ⊤)))
    (a : Fin n → Fin n → Γ(S, ⊤))
    (hmat : ∀ (U : S.Etale) (m : Γ((Modules.tensorPullback U.hom).obj E, ⊤)) (i : Fin n),
      e U (Fapp U m) i =
        ∑ j, (show Γ(U.left, ⊤) from U.hom.appTop (a i j)) * (e U m j) ^ p)
    (hnat : ∀ (U W : S.Etale) (g : W ⟶ U)
      (m : Γ((Modules.tensorPullback U.hom).obj E, ⊤)) (i : Fin n),
      e W (ρ g m) i = g.left.appTop (e U m i)) :
    ∃ c : ∀ U : S.Etale, K.obj.obj (op U) ≃
        {x : Fin n → Γ(U.left, ⊤) //
          ∀ i, x i = ∑ j, (show Γ(U.left, ⊤) from U.hom.appTop (a i j)) * x j ^ p},
      ∀ (U W : S.Etale) (g : W ⟶ U) (s : K.obj.obj (op U)) (i : Fin n),
        (c W (K.obj.map g.op s)).1 i = g.left.appTop ((c U s).1 i) := by
  refine ⟨fun U ↦ Equiv.ofBijective (fun s ↦ ⟨fun i ↦ e U (ι U s) i, fun i ↦
    (congrArg (fun y ↦ e U y i) (hfix U s)).symm.trans (hmat U _ i)⟩) ⟨?_, ?_⟩, ?_⟩
  · intro s t h
    apply hinj U
    apply (e U).injective
    funext i
    exact congrFun (congrArg Subtype.val h) i
  · intro x
    obtain ⟨s, hs⟩ := hsurj U ((e U).symm x.1) <| (e U).injective <| funext fun i ↦ by
      rw [hmat]
      simp only [LinearEquiv.apply_symm_apply]
      exact (x.2 i).symm
    refine ⟨s, Subtype.ext (funext fun i ↦ ?_)⟩
    simp [hs]
  · intro U W g s i
    exact (congrArg (fun y ↦ e W y i) (ConcreteCategory.congr_hom (hιnat g) s)).trans
      (hnat U W g _ i)

/-- The sections of the kernel of `F - 1` are the solutions of the Frobenius fixed-point
equations in the coordinates of a free frame, naturally in the étale test object. -/
theorem exists_frobenius_linear_free_kernel_coordinates
    (p : ℕ) (S : Scheme.{u}) (E : S.Modules) [E.IsQuasicoherent]
    (F : (Modules.etaleTensorSectionsSheaf E) ⟶ Modules.etaleTensorSectionsSheaf E)
    (hF : ∀ (U : S.Etale) (a : Γ(U.left, ⊤))
      (e : Γ((Modules.tensorPullback U.hom).obj E, ⊤)),
      F.hom.app (op U)
          ((((Modules.tensorPullback U.hom).obj E).smul a).asHom.hom e) =
        (((Modules.tensorPullback U.hom).obj E).smul (a ^ p)).asHom.hom
          (F.hom.app (op U) e))
    (n : ℕ) (α : E ≅
      SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))) :
    ∃ (a : Fin n → Fin n → Γ(S, ⊤))
      (c : ∀ U : S.Etale, (kernel (F - 𝟙 _)).obj.obj (op U) ≃
        {x : Fin n → Γ(U.left, ⊤) //
          ∀ i, x i = ∑ j, (show Γ(U.left, ⊤) from U.hom.appTop (a i j)) * x j ^ p}),
      ∀ (U W : S.Etale) (g : W ⟶ U) (s : (kernel (F - 𝟙 _)).obj.obj (op U)) (i : Fin n),
        (c W ((kernel (F - 𝟙 _)).obj.map g.op s)).1 i = g.left.appTop ((c U s).1 i) := by
  obtain ⟨e, hnat⟩ := exists_etale_free_frame_coordinates S E n α
  obtain ⟨a, hmat⟩ := exists_frobenius_matrix_aux E p n
    (fun g ↦ (Modules.etaleTensorSectionsSheaf E).obj.map g.op) (fun U ↦ F.hom.app (op U))
    (fun g ↦ F.hom.naturality g.op) hF e hnat
  refine ⟨a, exists_kernel_coordinates_aux E p n
    (kernel (F - 𝟙 (Modules.etaleTensorSectionsSheaf E)))
    (fun U ↦ (kernel.ι (F - 𝟙 (Modules.etaleTensorSectionsSheaf E))).hom.app (op U))
    (fun g ↦ (Modules.etaleTensorSectionsSheaf E).obj.map g.op)
    (fun g ↦ (kernel.ι (F - 𝟙 (Modules.etaleTensorSectionsSheaf E))).hom.naturality g.op)
    (fun U ↦ F.hom.app (op U))
    (fun U ↦ sheaf_kernel_ι_app_injective _ _) (fun U s ↦ ?_) (fun U m hm ↦ ?_)
    e a hmat hnat⟩
  · have h : kernel.ι (F - 𝟙 (Modules.etaleTensorSectionsSheaf E)) ≫ F =
        kernel.ι (F - 𝟙 (Modules.etaleTensorSectionsSheaf E)) := by
      simpa [Preadditive.comp_sub, sub_eq_zero] using
        kernel.condition (F - 𝟙 (Modules.etaleTensorSectionsSheaf E))
    exact ConcreteCategory.congr_hom (congrArg (fun φ ↦ φ.hom.app (op U)) h) s
  · refine sheaf_kernel_ι_app_surjective _ _ m ?_
    rw [sheaf_sub_hom_app_apply, hm]
    exact sub_eq_zero.mpr rfl

end AlgebraicGeometry.Scheme
