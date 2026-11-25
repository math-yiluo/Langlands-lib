import Langlands.GaloisCohomology.Local.EulerCharacteristic.Additive
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Descent
import Langlands.Cohomology.Profinite.Cup.Functoriality
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Change of scalars, twists, and the regular representation
-/

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace Langlands.ProfiniteCohomology

-- from Scalars.lean
open CategoryTheory groupCohomology


section Bridge

variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G] [TopologicalSpace G]

def cochainsAddEquiv {A : Rep.{u} k G} {A' : Rep.{u} k' G} (e : A ≃+ A') (n : ℕ) :
    locallyConstantCochains A n ≃+ locallyConstantCochains A' n where
  toFun x := ⟨fun g => e (x.1 g), x.2.comp e⟩
  invFun x := ⟨fun g => e.symm (x.1 g), x.2.comp e.symm⟩
  left_inv _ := Subtype.ext (funext fun _ => e.symm_apply_apply _)
  right_inv _ := Subtype.ext (funext fun _ => e.apply_symm_apply _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add e _ _)

@[simp]
theorem cochainsAddEquiv_apply {A : Rep.{u} k G} {A' : Rep.{u} k' G} (e : A ≃+ A') (n : ℕ)
    (x : locallyConstantCochains A n) (g : Fin n → G) :
    (cochainsAddEquiv e n x : (Fin n → G) → A') g = e ((x : (Fin n → G) → A) g) :=
  rfl

variable [IsTopologicalGroup G] {A : Rep.{u} k G} {A' : Rep.{u} k' G} [IsSmoothRep A]
  [IsSmoothRep A'] (e : A ≃+ A') (he : ∀ (g : G) (a : A), e (A.ρ g a) = A'.ρ g (e a))

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsSmoothRep A] [IsSmoothRep A'] in
include he in

theorem addEquiv_inhomogeneousCochains_d (i : ℕ) (f : (Fin i → G) → A) (g : Fin (i + 1) → G) :
    e ((inhomogeneousCochains.d A i).hom f g) =
      (inhomogeneousCochains.d A' i).hom (fun h => e (f h)) g := by
  rw [inhomogeneousCochains.d_hom_apply, inhomogeneousCochains.d_hom_apply, map_add, map_sum, he]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  have hk : ∀ (c : ℕ) (a : A), ((-1 : k) ^ c) • a = ((-1 : ℤ) ^ c) • a := fun c a => by
    rw [← Int.cast_smul_eq_zsmul k]
    push_cast
    rfl
  have hk' : ∀ (c : ℕ) (a : A'), ((-1 : k') ^ c) • a = ((-1 : ℤ) ^ c) • a := fun c a => by
    rw [← Int.cast_smul_eq_zsmul k']
    push_cast
    rfl
  rw [hk, hk', map_zsmul]

include he in

theorem cochainsAddEquiv_d (i j : ℕ) (x : (cochains A).X i) :
    cochainsAddEquiv e j (((cochains A).d i j).hom x) =
      ((cochains A').d i j).hom (cochainsAddEquiv e i x) := by
  rcases eq_or_ne (i + 1) j with rfl | hij
  · rw [cochains_d, cochains_d]
    apply Subtype.ext
    funext g
    exact addEquiv_inhomogeneousCochains_d e he i x.1 g
  · have h' : ¬ (ComplexShape.up ℕ).Rel i j := hij
    rw [HomologicalComplex.shape _ _ _ h', HomologicalComplex.shape _ _ _ h']
    exact map_zero _

noncomputable def cochainsAbIso (i : ℕ) :
    (forget₂ (ModuleCat.{u} k) Ab).obj ((cochains A).X i) ≅
      (forget₂ (ModuleCat.{u} k') Ab).obj ((cochains A').X i) :=
  (cochainsAddEquiv e i).toAddCommGrpIso

noncomputable def cochainsScAbIso (n : ℕ) :
    (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.obj ((cochains A).sc n) ≅
      (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.obj ((cochains A').sc n) :=
  ShortComplex.isoMk (cochainsAbIso e _) (cochainsAbIso e _) (cochainsAbIso e _)
    (by
      ext x
      exact (cochainsAddEquiv_d e he _ _ x).symm)
    (by
      ext x
      exact (cochainsAddEquiv_d e he _ _ x).symm)

end Bridge

section HomologyAb

variable {k k' : Type u} [CommRing k] [CommRing k']

noncomputable def homologyAbIsoOfAbIso {S₁ : ShortComplex (ModuleCat.{u} k)}
    {S₂ : ShortComplex (ModuleCat.{u} k')}
    (σ : (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.obj S₁ ≅
      (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.obj S₂) :
    (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{u} k) Ab).obj S₁ ≅
      (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{u} k') Ab).obj S₂ :=
  ((ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} k) Ab)).app S₁).symm ≪≫
    (ShortComplex.homologyFunctor Ab).mapIso σ ≪≫
    (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} k') Ab)).app S₂

theorem homologyMap_comp_homologyAbIsoOfAbIso
    {S₁ T₁ : ShortComplex (ModuleCat.{u} k)} {S₂ T₂ : ShortComplex (ModuleCat.{u} k')}
    (φ₁ : S₁ ⟶ T₁) (φ₂ : S₂ ⟶ T₂)
    (σS : (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.obj S₁ ≅
      (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.obj S₂)
    (σT : (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.obj T₁ ≅
      (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.obj T₂)
    (h : (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.map φ₁ ≫ σT.hom =
      σS.hom ≫ (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.map φ₂) :
    (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{u} k) Ab).map φ₁ ≫
        (homologyAbIsoOfAbIso σT).hom =
      (homologyAbIsoOfAbIso σS).hom ≫
        (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{u} k') Ab).map φ₂ := by
  have n1 := (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} k) Ab)).inv.naturality φ₁
  have n2 := (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} k') Ab)).hom.naturality φ₂
  have n3 : ((forget₂ (ModuleCat.{u} k) Ab).mapShortComplex ⋙
        ShortComplex.homologyFunctor Ab).map φ₁ ≫ (ShortComplex.homologyFunctor Ab).map σT.hom =
      (ShortComplex.homologyFunctor Ab).map σS.hom ≫
        ((forget₂ (ModuleCat.{u} k') Ab).mapShortComplex ⋙ ShortComplex.homologyFunctor Ab).map φ₂ := by
    rw [Functor.comp_map, Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp, h]
  simp only [homologyAbIsoOfAbIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  slice_lhs 1 2 => rw [n1]
  slice_lhs 2 3 => rw [n3]
  slice_lhs 3 4 => rw [n2]

end HomologyAb

section Cohomology

variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {A : Rep.{u} k G} {A' : Rep.{u} k' G} [IsSmoothRep A]
  [IsSmoothRep A'] (e : A ≃+ A') (he : ∀ (g : G) (a : A), e (A.ρ g a) = A'.ρ g (e a))

noncomputable def cohomologyAddEquivOfEquiv (n : ℕ) : cohomology A n ≃+ cohomology A' n :=
  (homologyAbIsoOfAbIso (cochainsScAbIso e he n)).addCommGroupIsoToAddEquiv

theorem cohomologyAddEquivOfEquiv_mapAlong {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : H →ₜ* G) {B : Rep.{u} k H} {B' : Rep.{u} k' H}
    [IsSmoothRep B] [IsSmoothRep B'] (eB : B ≃+ B')
    (heB : ∀ (h : H) (b : B), eB (B.ρ h b) = B'.ρ h (eB b))
    (f : Rep.res (φ : H →* G) A ⟶ B) (f' : Rep.res (φ : H →* G) A' ⟶ B')
    (hf : ∀ a : A, eB (f.hom a) = f'.hom (e a)) (n : ℕ) (x : cohomology A n) :
    cohomologyAddEquivOfEquiv eB heB n ((map φ f n).hom x) =
      (map φ f' n).hom (cohomologyAddEquivOfEquiv e he n x) := by
  have key := homologyMap_comp_homologyAbIsoOfAbIso
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (cochainsMap φ f))
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (cochainsMap φ f'))
    (cochainsScAbIso e he n) (cochainsScAbIso eB heB n) (by
      ext x <;> exact Subtype.ext (funext fun _ => hf _))
  exact congrArg (fun f => f.hom x) key

theorem cohomologyAddEquivOfEquiv_cohomologyRes (S : Subgroup G) (n : ℕ) (x : cohomology A n) :
    cohomologyAddEquivOfEquiv (A := Rep.res S.subtype A) (A' := Rep.res S.subtype A') e
        (fun s a => he s a) n ((res A S n).hom x) =
      (res A' S n).hom (cohomologyAddEquivOfEquiv e he n x) := by
  rw [res_eq, res_eq]
  exact cohomologyAddEquivOfEquiv_mapAlong e he (subgroupInclusion S)
    (B := Rep.res S.subtype A) (B' := Rep.res S.subtype A') e (fun s a => he s a) (𝟙 _) (𝟙 _)
    (fun _ => rfl) n x

theorem cohomologyAddEquivOfEquiv_cohomologyMap {B : Rep.{u} k G} {B' : Rep.{u} k' G}
    [IsSmoothRep B] [IsSmoothRep B'] (eB : B ≃+ B')
    (heB : ∀ (g : G) (b : B), eB (B.ρ g b) = B'.ρ g (eB b))
    (f : A ⟶ B) (f' : A' ⟶ B') (hf : ∀ a : A, eB (f.hom a) = f'.hom (e a)) (n : ℕ)
    (x : cohomology A n) :
    cohomologyAddEquivOfEquiv eB heB n ((coeffMap f n).hom x) =
      (coeffMap f' n).hom (cohomologyAddEquivOfEquiv e he n x) := by
  exact cohomologyAddEquivOfEquiv_mapAlong e he (.id G) eB heB f f' hf n x

theorem cohomologyAddEquivOfEquiv_cohomologyConj (N : Subgroup G) [N.Normal] (n : ℕ) (g : G)
    (x : cohomology (Rep.res N.subtype A) n) :
    cohomologyAddEquivOfEquiv (A := Rep.res N.subtype A) (A' := Rep.res N.subtype A') e
        (fun s a => he s a) n ((cohomologyConj A N n g).hom x) =
      (cohomologyConj A' N n g).hom
        (cohomologyAddEquivOfEquiv (A := Rep.res N.subtype A) (A' := Rep.res N.subtype A') e
          (fun s a => he s a) n x) :=
  cohomologyAddEquivOfEquiv_mapAlong (A := Rep.res N.subtype A) (A' := Rep.res N.subtype A') e
    (fun s a => he s a) ⟨conjHom N g, continuous_conjHom N g⟩
    (B := Rep.res N.subtype A) (B' := Rep.res N.subtype A') e (fun s a => he s a)
    (conjMor A N g) (conjMor A' N g) (fun a => he g a) n x

end Cohomology

section ZMod

variable {G : Type u} [Group G] (l : ℕ) (A : Rep.{u} (ULift.{u} ℤ) G)
  (hA : ∀ a : A, l • a = 0)

noncomputable def zmodRepOfTorsion : Rep.{u} (ULift.{u} (ZMod l)) G :=
  letI : Module (ZMod l) A := AddCommGroup.zmodModule hA
  Rep.of (X := A)
    { toFun := fun g =>
        { toFun := fun a => A.ρ g a
          map_add' := fun a b => map_add (A.ρ g) a b
          map_smul' := fun c a =>
            ((A.ρ g).toAddMonoidHom.toZModLinearMap l).map_smul c.down a }
      map_one' := by
        ext a
        simp
      map_mul' := fun g h => by
        ext a
        change A.ρ (g * h) a = A.ρ g (A.ρ h a)
        rw [map_mul, Module.End.mul_apply] }

theorem zmodRepOfTorsion_ρ_apply (g : G) (a : A) :
    (zmodRepOfTorsion l A hA).ρ g a = A.ρ g a :=
  rfl

def zmodRepOfTorsionEquiv : A ≃+ zmodRepOfTorsion l A hA :=
  AddEquiv.refl A

theorem zmodRepOfTorsionEquiv_apply (a : A) : zmodRepOfTorsionEquiv l A hA a = a :=
  rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

instance isSmoothRep_zmodRepOfTorsion [IsSmoothRep A] :
    IsSmoothRep (zmodRepOfTorsion l A hA) :=
  IsSmoothRep.of_isOpen_stabilizer _ fun a => IsSmoothRep.isOpen_stabilizer A a

variable [IsSmoothRep A]

noncomputable def cohomologyZModEquiv (n : ℕ) :
    cohomology A n ≃+ cohomology (zmodRepOfTorsion l A hA) n :=
  cohomologyAddEquivOfEquiv (zmodRepOfTorsionEquiv l A hA) (fun _ _ => rfl) n

end ZMod

-- from TwistDefs.lean
open CategoryTheory MonoidalCategory


variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Smul

variable {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B]

theorem cochainsMap_smul (c : k) (f : A ⟶ B) : coeffCochainsMap (c • f) = c • coeffCochainsMap f := by
  ext n x : 3
  apply Subtype.ext
  funext y
  rfl

set_option backward.isDefEq.respectTransparency false in
-- `coeffMap` is `map (.id G)`: its source `Rep.res ↑(.id G) A` is definitionally but not reducibly
-- `A` at Lean 4.35, which the `change` to homology maps needs (as for `groupCohomology.map` in Mathlib).
theorem cohomologyMap_smul (c : k) (f : A ⟶ B) (n : ℕ) :
    coeffMap (c • f) n = c • coeffMap f n := by
  change HomologicalComplex.homologyMap (coeffCochainsMap (c • f)) n =
    c • HomologicalComplex.homologyMap (coeffCochainsMap f) n
  rw [cochainsMap_smul]
  change ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (c • coeffCochainsMap f)) =
    c • ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (coeffCochainsMap f))
  rw [← ShortComplex.homologyMap_smul]
  rfl

end Smul

section Morphisms

variable (T : Rep.{u} k G) {M : Rep.{u} k G}

omit [TopologicalSpace G] [IsTopologicalGroup G] in

noncomputable def tensorRightMor (m : M) (hm : ∀ g : G, M.ρ g m = m) : T ⟶ T ⊗ M :=
  Rep.ofHom ⟨(TensorProduct.mk k T M).flip m, fun g => by
    ext t
    simp [Representation.tprod_apply, hm g]⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem tensorRightMor_hom_apply (m : M) (hm : ∀ g : G, M.ρ g m = m) (t : T) :
    (tensorRightMor T m hm).hom t = t ⊗ₜ[k] m :=
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in

noncomputable def tensorFormMor (f : M →ₗ[k] k) (hf : ∀ (g : G) (m : M), f (M.ρ g m) = f m) :
    T ⊗ M ⟶ T :=
  Rep.ofHom ⟨(TensorProduct.rid k T).toLinearMap ∘ₗ LinearMap.lTensor T f, fun g => by
    ext t m
    simp [Representation.tprod_apply, hf g]⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem tensorFormMor_hom_tmul (f : M →ₗ[k] k) (hf : ∀ (g : G) (m : M), f (M.ρ g m) = f m)
    (t : T) (m : M) : (tensorFormMor T f hf).hom (t ⊗ₜ[k] m) = f m • t := by
  simp [tensorFormMor]

end Morphisms

section TwistMap

variable (T : Rep.{u} k G) [IsSmoothRep T] {M : Rep.{u} k G} [IsSmoothRep M]
  (hM : ∀ (g : G) (m : M), M.ρ g m = m)

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsSmoothRep T] [IsSmoothRep M] in
theorem tensorRightMor_add (m m' : M) :
    tensorRightMor T (m + m') (fun g => hM g _) =
      tensorRightMor T m (fun g => hM g m) + tensorRightMor T m' (fun g => hM g m') := by
  ext t
  change t ⊗ₜ[k] (m + m') = t ⊗ₜ[k] m + t ⊗ₜ[k] m'
  exact TensorProduct.tmul_add _ _ _

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsSmoothRep T] [IsSmoothRep M] in
theorem tensorRightMor_smul (c : k) (m : M) :
    tensorRightMor T (c • m) (fun g => hM g _) = c • tensorRightMor T m (fun g => hM g m) := by
  ext t
  change t ⊗ₜ[k] (c • m) = c • t ⊗ₜ[k] m
  exact TensorProduct.tmul_smul _ _ _

noncomputable def twistMap (n : ℕ) :
    TensorProduct k (cohomology T n) M →ₗ[k] cohomology (T ⊗ M) n :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun m => (coeffMap (tensorRightMor T m (fun g => hM g m)) n).hom x
          map_add' := fun m m' => by
            rw [tensorRightMor_add T hM, cohomologyMap_add]
            rfl
          map_smul' := fun c m => by
            rw [tensorRightMor_smul T hM, cohomologyMap_smul, ModuleCat.hom_smul,
              LinearMap.smul_apply, RingHom.id_apply] }
      map_add' := fun x y => by
        ext m
        simp
      map_smul' := fun c x => by
        ext m
        simp }

theorem twistMap_tmul (n : ℕ) (x : cohomology T n) (m : M) :
    twistMap T hM n (x ⊗ₜ[k] m) = (coeffMap (tensorRightMor T m (fun g => hM g m)) n).hom x :=
  rfl

end TwistMap

section Subgroup

variable (N : Subgroup G) (T M : Rep.{u} k G)

variable [IsSmoothRep T] [IsSmoothRep M] (hM : ∀ (g : N) (m : M), M.ρ g m = m)

noncomputable def twistResMap (n : ℕ) :
    TensorProduct k (cohomology (Rep.res N.subtype T) n) M →ₗ[k]
      cohomology (Rep.res N.subtype (T ⊗ M)) n :=
  (coeffMap (resTensorIso N.subtype T M).inv n).hom ∘ₗ
    twistMap (M := Rep.res N.subtype M) (Rep.res N.subtype T) hM n

theorem twistResMap_tmul (n : ℕ) (x : cohomology (Rep.res N.subtype T) n) (m : M) :
    twistResMap N T M hM n (x ⊗ₜ[k] m) =
      (coeffMap (tensorRightMor (M := Rep.res N.subtype M) (Rep.res N.subtype T) m
        (fun g => hM g m) ≫ (resTensorIso N.subtype T M).inv) n).hom x := by
  rw [coeffMap_comp]
  rfl

end Subgroup

-- from CohomologyMapTensorRightMorCompCohomologyConj.lean
open CategoryTheory MonoidalCategory


variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Equiv

variable (T : Rep.{u} k G) [IsSmoothRep T] {M : Rep.{u} k G} [IsSmoothRep M]
  (hM : ∀ (g : G) (m : M), M.ρ g m = m)

include hM

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsSmoothRep T] [IsSmoothRep M] in

theorem form_invariant_of_forall_eq (f : M →ₗ[k] k) (g : G) (m : M) : f (M.ρ g m) = f m := by
  rw [hM]

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsSmoothRep T] [IsSmoothRep M] in

theorem tensorRightMor_comp_tensorFormMor (m : M) (f : M →ₗ[k] k) :
    tensorRightMor T m (fun g => hM g m) ≫
        tensorFormMor T f (form_invariant_of_forall_eq hM f) = f m • 𝟙 T := by
  ext t
  change f m • t = f m • t
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsSmoothRep T] [IsSmoothRep M] in

theorem sum_tensorFormMor_comp_tensorRightMor {ι : Type*} [Fintype ι] (b : Module.Basis ι k M) :
    ∑ i, tensorFormMor T (b.coord i) (form_invariant_of_forall_eq hM _) ≫
        tensorRightMor T (b i) (fun g => hM g (b i)) = 𝟙 (T ⊗ M) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro t m
  rw [Rep.sum_hom, Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply]
  change ∑ i, (b.coord i m • t) ⊗ₜ[k] b i = t ⊗ₜ[k] m
  simp_rw [Module.Basis.coord_apply, TensorProduct.smul_tmul]
  rw [← TensorProduct.tmul_sum, b.sum_repr]

noncomputable def twistInv {ι : Type*} [Fintype ι] (b : Module.Basis ι k M) (n : ℕ) :
    cohomology (T ⊗ M) n →ₗ[k] TensorProduct k (cohomology T n) M :=
  ∑ i, (TensorProduct.mk k (cohomology T n) M).flip (b i) ∘ₗ
    (coeffMap (tensorFormMor T (b.coord i) (form_invariant_of_forall_eq hM _)) n).hom

theorem twistMap_comp_twistInv {ι : Type*} [Fintype ι] (b : Module.Basis ι k M) (n : ℕ) :
    twistMap T hM n ∘ₗ twistInv T hM b n = LinearMap.id := by
  ext y
  simp only [twistInv, LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
    LinearMap.flip_apply, TensorProduct.mk_apply, twistMap_tmul, LinearMap.id_apply]
  simp_rw [← ModuleCat.comp_apply, ← coeffMap_comp]
  rw [← LinearMap.sum_apply, ← ModuleCat.hom_sum, ← cohomologyMap_sum,
    sum_tensorFormMor_comp_tensorRightMor, coeffMap_id]
  rfl

theorem twistInv_comp_twistMap {ι : Type*} [Fintype ι] (b : Module.Basis ι k M) (n : ℕ) :
    twistInv T hM b n ∘ₗ twistMap T hM n = LinearMap.id := by
  apply TensorProduct.ext'
  intro x m
  simp only [twistInv, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply, twistMap_tmul, LinearMap.id_apply]
  simp_rw [← ModuleCat.comp_apply, ← coeffMap_comp, tensorRightMor_comp_tensorFormMor,
    cohomologyMap_smul, coeffMap_id, ModuleCat.hom_smul, LinearMap.smul_apply,
    Module.Basis.coord_apply, TensorProduct.smul_tmul]
  rw [← TensorProduct.tmul_sum, b.sum_repr]
  rfl

noncomputable def twistEquiv [Module.Free k M] [Module.Finite k M] (n : ℕ) :
    TensorProduct k (cohomology T n) M ≃ₗ[k] cohomology (T ⊗ M) n :=
  LinearEquiv.ofLinearMap (twistMap T hM n) (twistInv T hM (Module.Free.chooseBasis k M) n)
    (twistMap_comp_twistInv T hM _ n) (twistInv_comp_twistMap T hM _ n)

theorem twistMap_bijective [Module.Free k M] [Module.Finite k M] (n : ℕ) :
    Function.Bijective (twistMap T hM n) :=
  (twistEquiv T hM n).bijective

end Equiv

section Subgroup

variable (N : Subgroup G) (T M : Rep.{u} k G) [IsSmoothRep T] [IsSmoothRep M]
  (hM : ∀ (g : N) (m : M), M.ρ g m = m)

theorem cohomologyMap_resTensorIso_inv_bijective (n : ℕ) :
    Function.Bijective (coeffMap (resTensorIso N.subtype T M).inv n).hom := by
  refine Function.bijective_iff_has_inverse.2
    ⟨(coeffMap (resTensorIso N.subtype T M).hom n).hom, fun x => ?_, fun x => ?_⟩
  · rw [← ModuleCat.comp_apply, ← coeffMap_comp, Iso.inv_hom_id, coeffMap_id]
    rfl
  · rw [← ModuleCat.comp_apply, ← coeffMap_comp, Iso.hom_inv_id, coeffMap_id]
    rfl

noncomputable def twistResEquiv [Module.Free k M] [Module.Finite k M] (n : ℕ) :
    TensorProduct k (cohomology (Rep.res N.subtype T) n) M ≃ₗ[k]
      cohomology (Rep.res N.subtype (T ⊗ M)) n :=
  LinearEquiv.ofBijective (twistResMap N T M hM n)
    ((cohomologyMap_resTensorIso_inv_bijective N T M n).comp
      (twistMap_bijective (M := Rep.res N.subtype M) (Rep.res N.subtype T) hM n))

theorem twistResEquiv_apply [Module.Free k M] [Module.Finite k M] (n : ℕ)
    (z : TensorProduct k (cohomology (Rep.res N.subtype T) n) M) :
    twistResEquiv N T M hM n z = twistResMap N T M hM n z :=
  rfl

variable [N.Normal]

set_option backward.isDefEq.respectTransparency false in
-- A coefficient map used at the types `Rep.res ↑(.id _) A` and `A`, definitionally but not
-- reducibly equal at Lean 4.35, has to be identified for `map_comp` to apply.
theorem cohomologyMap_tensorRightMor_comp_cohomologyConj (n : ℕ) (g : G) (m : M) :
    coeffMap (tensorRightMor (M := Rep.res N.subtype M) (Rep.res N.subtype T) m
        (fun h => hM h m) ≫ (resTensorIso N.subtype T M).inv) n ≫ cohomologyConj (T ⊗ M) N n g =
      cohomologyConj T N n g ≫
        coeffMap (tensorRightMor (M := Rep.res N.subtype M) (Rep.res N.subtype T) (M.ρ g m)
          (fun h => hM h _) ≫ (resTensorIso N.subtype T M).inv) n := by
  rw [coeffMap_eq, coeffMap_eq,
    cohomologyConj, cohomologyConj, ← map_comp, ← map_comp]
  refine ProfiniteCohomology.map_congr _ _ (ContinuousMonoidHom.ext fun s => rfl) (fun a => ?_) n
  change (T ⊗ M).ρ g (a ⊗ₜ[k] m) = T.ρ g a ⊗ₜ[k] M.ρ g m
  rfl

theorem cohomologyConj_twistResMap_tmul (n : ℕ) (g : G)
    (x : cohomology (Rep.res N.subtype T) n) (m : M) :
    (cohomologyConj (T ⊗ M) N n g).hom (twistResMap N T M hM n (x ⊗ₜ[k] m)) =
      twistResMap N T M hM n ((cohomologyConj T N n g).hom x ⊗ₜ[k] M.ρ g m) := by
  rw [twistResMap_tmul, twistResMap_tmul, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    cohomologyMap_tensorRightMor_comp_cohomologyConj]

theorem cohomologyConj_comp_twistResMap (n : ℕ) (g : G) :
    (cohomologyConj (T ⊗ M) N n g).hom ∘ₗ twistResMap N T M hM n =
      twistResMap N T M hM n ∘ₗ TensorProduct.map (cohomologyConj T N n g).hom (M.ρ g) := by
  apply TensorProduct.ext'
  intro x m
  rw [LinearMap.comp_apply, LinearMap.comp_apply, TensorProduct.map_tmul]
  exact cohomologyConj_twistResMap_tmul N T M hM n g x m

theorem cohomologyConj_twistResEquiv [Module.Free k M] [Module.Finite k M] (n : ℕ) (g : G)
    (z : TensorProduct k (cohomology (Rep.res N.subtype T) n) M) :
    (cohomologyConj (T ⊗ M) N n g).hom (twistResEquiv N T M hM n z) =
      twistResEquiv N T M hM n (TensorProduct.map (cohomologyConj T N n g).hom (M.ρ g) z) :=
  LinearMap.congr_fun (cohomologyConj_comp_twistResMap N T M hM n g) z

noncomputable def quotientRep : Representation k (G ⧸ N) M :=
  QuotientGroup.lift N M.ρ fun g hg => by
    ext m
    exact hM ⟨g, hg⟩ m

omit [IsSmoothRep T] [IsSmoothRep M] [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem quotientRep_mk (g : G) (m : M) : quotientRep N M hM (g : G ⧸ N) m = M.ρ g m :=
  rfl

variable [CompactSpace N]

theorem twistResEquiv_cohomologyConjRep [Module.Free k M] [Module.Finite k M] (n : ℕ)
    (q : G ⧸ N) (z : TensorProduct k (cohomology (Rep.res N.subtype T) n) M) :
    cohomologyConjRep (T ⊗ M) N n q (twistResEquiv N T M hM n z) =
      twistResEquiv N T M hM n
        (((cohomologyConjRep T N n).tprod (quotientRep N M hM)) q z) := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [cohomologyConjRep_mk, cohomologyConj_twistResEquiv, Representation.tprod_apply]
    congr 2
    apply TensorProduct.ext'
    intro x m
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, cohomologyConjRep_mk, quotientRep_mk]

noncomputable def twistInvariantsEquiv [Module.Free k M] [Module.Finite k M] (n : ℕ) :
    ((cohomologyConjRep T N n).tprod (quotientRep N M hM)).invariants ≃ₗ[k]
      cohomologyConjInvariants (T ⊗ M) N n :=
  (twistResEquiv N T M hM n).ofSubmodules _ _ (by
    ext y
    rw [Submodule.mem_map_equiv, mem_cohomologyConjInvariants_iff, Representation.mem_invariants,
      Representation.mem_invariants]
    refine ⟨fun h q => ?_, fun h q => ?_⟩
    · rw [← LinearEquiv.apply_symm_apply (twistResEquiv N T M hM n) y,
        twistResEquiv_cohomologyConjRep, h q]
    · apply (twistResEquiv N T M hM n).injective
      rw [← twistResEquiv_cohomologyConjRep, LinearEquiv.apply_symm_apply, h q])

theorem twistInvariantsEquiv_apply [Module.Free k M] [Module.Finite k M] (n : ℕ)
    (z : ((cohomologyConjRep T N n).tprod (quotientRep N M hM)).invariants) :
    (twistInvariantsEquiv N T M hM n z : cohomology (Rep.res N.subtype (T ⊗ M)) n) =
      twistResEquiv N T M hM n z :=
  rfl

end Subgroup

-- from CoprimeRegular.lean
open Representation TensorProduct

section Regular

variable {k Γ N : Type*} [CommRing k] [Group Γ] [Fintype Γ] [DecidableEq Γ] [AddCommGroup N]
  [Module k N] (σ : Representation k Γ N)

noncomputable def regularTensorEquiv : MonoidAlgebra k Γ ⊗[k] N ≃ₗ[k] (Γ →₀ N) :=
  TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv k) (LinearEquiv.refl k N) ≪≫ₗ
    finsuppScalarLeft k N Γ

omit [Group Γ] [Fintype Γ] in
theorem regularTensorEquiv_single_tmul (g : Γ) (r : k) (n : N) :
    regularTensorEquiv (MonoidAlgebra.single g r ⊗ₜ[k] n) = Finsupp.single g (r • n) := by
  ext γ
  rw [regularTensorEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    finsuppScalarLeft_apply_tmul_apply]
  change (MonoidAlgebra.coeffAddEquiv (MonoidAlgebra.single g r)) γ • n = _
  rw [show MonoidAlgebra.coeffAddEquiv (MonoidAlgebra.single g r) = Finsupp.single g r from rfl,
    Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

omit [Fintype Γ] in

theorem regularTensorEquiv_tprod_apply (h : Γ) (x : MonoidAlgebra k Γ ⊗[k] N) (γ : Γ) :
    regularTensorEquiv (((leftRegular k Γ).tprod σ) h x) γ =
      σ h (regularTensorEquiv x (h⁻¹ * γ)) := by
  induction x using TensorProduct.inductionOn with
  | tmul p n =>
    induction p using MonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq =>
      rw [TensorProduct.add_tmul, map_add, map_add, Finsupp.add_apply, hp, hq, map_add,
        Finsupp.add_apply, map_add]
    | single g r =>
      rw [Representation.tprod_apply, TensorProduct.map_tmul, ofMulAction_single, regularTensorEquiv_single_tmul,
        regularTensorEquiv_single_tmul, Finsupp.single_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases hg : h * g = γ
      · subst hg
        simp
      · have : ¬ g = h⁻¹ * γ := fun e => hg (by rw [e, mul_inv_cancel_left])
        simp [hg, this]
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]

omit [Fintype Γ] in
theorem mem_invariants_regular_iff (x : MonoidAlgebra k Γ ⊗[k] N) :
    x ∈ ((leftRegular k Γ).tprod σ).invariants ↔
      ∀ γ, regularTensorEquiv x γ = σ γ (regularTensorEquiv x 1) := by
  rw [mem_invariants]
  constructor
  · intro hx γ
    conv_lhs => rw [← hx γ]
    rw [regularTensorEquiv_tprod_apply, inv_mul_cancel]
  · intro hx h
    apply regularTensorEquiv.injective
    ext γ
    rw [regularTensorEquiv_tprod_apply, hx (h⁻¹ * γ), hx γ, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel_left]

noncomputable def regularInvariantOf : N →ₗ[k] MonoidAlgebra k Γ ⊗[k] N :=
  regularTensorEquiv.symm.toLinearMap ∘ₗ (Finsupp.linearEquivFunOnFinite k N Γ).symm.toLinearMap ∘ₗ
    LinearMap.pi fun γ => σ γ

theorem regularTensorEquiv_regularInvariantOf (n : N) (γ : Γ) :
    regularTensorEquiv (regularInvariantOf σ n) γ = σ γ n := by
  simp [regularInvariantOf]

theorem regularInvariantOf_mem (n : N) :
    regularInvariantOf σ n ∈ ((leftRegular k Γ).tprod σ).invariants := by
  rw [mem_invariants_regular_iff]
  intro γ
  rw [regularTensorEquiv_regularInvariantOf, regularTensorEquiv_regularInvariantOf, map_one,
    Module.End.one_apply]

noncomputable def invariantsLeftRegularTensorEquiv :
    ((leftRegular k Γ).tprod σ).invariants ≃ₗ[k] N where
  toFun x := regularTensorEquiv (x : MonoidAlgebra k Γ ⊗[k] N) 1
  map_add' x y := by simp
  map_smul' c x := by simp
  invFun n := ⟨regularInvariantOf σ n, regularInvariantOf_mem σ n⟩
  left_inv x := by
    apply Subtype.ext
    apply regularTensorEquiv.injective
    ext γ
    simp only
    rw [regularTensorEquiv_regularInvariantOf, ← (mem_invariants_regular_iff σ _).1 x.2 γ]
  right_inv n := by
    simp only
    rw [regularTensorEquiv_regularInvariantOf, map_one, Module.End.one_apply]

theorem finrank_invariants_leftRegular_tprod :
    Module.finrank k ((leftRegular k Γ).tprod σ).invariants = Module.finrank k N :=
  (invariantsLeftRegularTensorEquiv σ).finrank_eq

end Regular

section Comp

variable {k Γ₁ Γ₂ X : Type*} [CommRing k] [Group Γ₁] [Group Γ₂] [AddCommGroup X] [Module k X]

theorem invariants_comp_of_surjective (ρ : Representation k Γ₁ X) (e : Γ₂ →* Γ₁)
    (he : Function.Surjective e) :
    Representation.invariants (ρ.comp e) = ρ.invariants := by
  ext x
  simp only [mem_invariants]
  exact ⟨fun h γ => by obtain ⟨δ, rfl⟩ := he γ; exact h δ, fun h δ => h (e δ)⟩

end Comp

-- from CoprimeTwist.lean
open CategoryTheory MonoidalCategory Representation


section Eval

variable {k G : Type u} [Field k] [Group G]

noncomputable abbrev homRep (T M : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (T.ρ.linHom M.ρ)

theorem homRep_ρ_apply (T M : Rep.{u} k G) (g : G) (f : T →ₗ[k] M) :
    (homRep T M).ρ g f = M.ρ g ∘ₗ f ∘ₗ T.ρ g⁻¹ :=
  rfl

noncomputable def evalMor (T M : Rep.{u} k G) : T ⊗ homRep T M ⟶ M :=
  Rep.ofHom ⟨TensorProduct.lift (LinearMap.applyₗ (R := k) (M := T) (M₂ := M)), fun g => by
    ext t f
    change (M.ρ g ∘ₗ f ∘ₗ T.ρ g⁻¹) (T.ρ g t) = M.ρ g (f t)
    simp only [LinearMap.comp_apply]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]⟩

theorem evalMor_hom_tmul (T M : Rep.{u} k G) (t : T) (f : T →ₗ[k] M) :
    (evalMor T M).hom (t ⊗ₜ[k] f) = f t :=
  rfl

theorem evalMor_bijective (T M : Rep.{u} k G) (hT : Module.finrank k T = 1) :
    Function.Bijective (evalMor T M).hom := by
  have : Module.Finite k T := Module.finite_of_finrank_eq_succ hT
  let b : Module.Basis (Fin 1) k T := Module.finBasisOfFinrankEq k T hT
  set t₀ := b 0
  have ht : ∀ t : T, b.coord 0 t • t₀ = t := fun t => by
    simpa using b.sum_repr t
  have hext : ∀ f g : T →ₗ[k] M, f t₀ = g t₀ → f = g := fun f g h =>
    b.ext fun i => by fin_cases i; exact h
  let φ : TensorProduct k T (T →ₗ[k] M) →ₗ[k] (T →ₗ[k] M) :=
    TensorProduct.lift (LinearMap.lsmul k (T →ₗ[k] M) ∘ₗ b.coord 0)
  have hφ : ∀ x : TensorProduct k T (T →ₗ[k] M), t₀ ⊗ₜ[k] φ x = x := fun x => by
    induction x using TensorProduct.inductionOn with
    | tmul t f =>
      simp only [φ, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply]
      rw [← TensorProduct.smul_tmul, ht]
    | add x y hx hy => rw [map_add, TensorProduct.tmul_add, hx, hy]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : φ x = 0 := hext _ _ (by
      rw [← hφ x, evalMor_hom_tmul] at hx
      simpa using hx)
    rw [← hφ x, h0, TensorProduct.tmul_zero]
  · intro m
    refine ⟨t₀ ⊗ₜ[k] b.constr k (fun _ => m), ?_⟩
    change b.constr k (fun _ => m) (b 0) = m
    rw [Module.Basis.constr_basis]

noncomputable def evalInv (T M : Rep.{u} k G) (hT : Module.finrank k T = 1) :
    M ⟶ T ⊗ homRep T M :=
  let e := LinearEquiv.ofBijective (evalMor T M).hom.toLinearMap (evalMor_bijective T M hT)
  Rep.ofHom ⟨e.symm.toLinearMap, fun g => by
    ext m
    apply e.injective
    change e (e.symm (M.ρ g m)) = (evalMor T M).hom ((T ⊗ homRep T M).ρ g (e.symm m))
    rw [LinearEquiv.apply_symm_apply, (evalMor T M).hom.isIntertwining]
    change M.ρ g m = M.ρ g (e (e.symm m))
    rw [LinearEquiv.apply_symm_apply]⟩

theorem evalInv_comp_evalMor (T M : Rep.{u} k G) (hT : Module.finrank k T = 1) :
    evalInv T M hT ≫ evalMor T M = 𝟙 M := by
  ext m
  exact (LinearEquiv.ofBijective (evalMor T M).hom.toLinearMap
    (evalMor_bijective T M hT)).apply_symm_apply m

theorem evalMor_comp_evalInv (T M : Rep.{u} k G) (hT : Module.finrank k T = 1) :
    evalMor T M ≫ evalInv T M hT = 𝟙 _ := by
  ext x
  exact (LinearEquiv.ofBijective (evalMor T M).hom.toLinearMap
    (evalMor_bijective T M hT)).symm_apply_apply x

end Eval

section Descent

variable {k G : Type u} [Field k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (P : OpenSubgroup G) [(P : Subgroup G).Normal] (T M : Rep.{u} k G)
  [IsSmoothRep T] [IsSmoothRep M]
  (hT : ∀ (g : (P : Subgroup G)) (t : T), T.ρ g t = t)
  (hM : ∀ (g : (P : Subgroup G)) (m : M), M.ρ g m = m)

omit [IsTopologicalGroup G] [CompactSpace G] [(P : Subgroup G).Normal] [IsSmoothRep T]
  [IsSmoothRep M] in
include hT hM in

theorem homRep_ρ_of_mem (g : (P : Subgroup G)) (f : homRep T M) : (homRep T M).ρ g f = f := by
  apply LinearMap.ext
  intro t
  change M.ρ g (f (T.ρ (g : G)⁻¹ t)) = f t
  rw [hM, show ((g : G)⁻¹) = ((g⁻¹ : (P : Subgroup G)) : G) from rfl, hT]

omit [CompactSpace G] [(P : Subgroup G).Normal] [IsSmoothRep T] [IsSmoothRep M] in
include hT hM in

theorem isSmoothRep_homRep : IsSmoothRep (homRep T M) :=
  IsSmoothRep.of_isOpen_stabilizer _ fun f => Subgroup.isOpen_mono (H₁ := (P : Subgroup G))
    (fun g hg => (mem_vectorStabilizer _ _ _).2 (homRep_ρ_of_mem P T M hT hM ⟨g, hg⟩ f)) P.isOpen

theorem bijective_nsmul_of_ne_zero {V : Type*} [AddCommGroup V] [Module k V] {m : ℕ}
    (hm : (m : k) ≠ 0) : Function.Bijective fun v : V => m • v := by
  have h : (fun v : V => m • v) = fun v => (m : k) • v := funext fun v => (Nat.cast_smul_eq_nsmul k m v).symm
  rw [h]
  refine ⟨fun v w hvw => ?_, fun v => ⟨(m : k)⁻¹ • v, by simp [smul_smul, mul_inv_cancel₀ hm]⟩⟩
  have := congrArg (fun x => (m : k)⁻¹ • x) hvw
  simpa [smul_smul, inv_mul_cancel₀ hm] using this

variable [Module.Finite k M] (hTr : Module.finrank k T = 1)
  (hP : ((P : Subgroup G).index : k) ≠ 0)

noncomputable def coprimeTwistEquiv (n : ℕ) :
    haveI := isSmoothRep_homRep P T M hT hM
    cohomology M n ≃ₗ[k]
      ((cohomologyConjRep T (P : Subgroup G) n).tprod
        (quotientRep (P : Subgroup G) (homRep T M) (homRep_ρ_of_mem P T M hT hM))).invariants :=
  haveI := isSmoothRep_homRep P T M hT hM
  haveI : Module.Finite k T := Module.finite_of_finrank_eq_succ hTr
  haveI : Module.Finite k (homRep T M) := inferInstanceAs (Module.Finite k (T →ₗ[k] M))
  (LinearEquiv.ofLinearMap (coeffMap (evalInv T M hTr) n).hom (coeffMap (evalMor T M) n).hom
      (by
        rw [← ModuleCat.hom_comp, ← coeffMap_comp, evalMor_comp_evalInv, coeffMap_id]
        rfl)
      (by
        rw [← ModuleCat.hom_comp, ← coeffMap_comp, evalInv_comp_evalMor, coeffMap_id]
        rfl)) ≪≫ₗ
    coprimeDescentEquiv P (T ⊗ homRep T M) (bijective_nsmul_of_ne_zero hP) n ≪≫ₗ
    (twistInvariantsEquiv (P : Subgroup G) T (homRep T M) (homRep_ρ_of_mem P T M hT hM) n).symm

include hTr hP in

theorem finrank_cohomology_eq_finrank_invariants (n : ℕ) :
    Module.finrank k (cohomology M n) = Module.finrank k
      ((cohomologyConjRep T (P : Subgroup G) n).tprod
        (quotientRep (P : Subgroup G) (homRep T M) (homRep_ρ_of_mem P T M hT hM))).invariants :=
  (coprimeTwistEquiv P T M hT hM hTr hP n).finrank_eq

end Descent

section Invariants

/-- Pulling back the first factor along an isomorphism `Γ₁ ≃* Γ₂` and pushing the second one
forward does not change the dimension of the invariants of a tensor product. -/
theorem finrank_invariants_tprod_comp_mulEquiv {k Γ₁ Γ₂ X N : Type*} [Field k] [Group Γ₁]
    [Group Γ₂] [AddCommGroup X] [Module k X] [AddCommGroup N] [Module k N]
    (ρ : Representation k Γ₂ X) (σ : Representation k Γ₁ N) (e : Γ₁ ≃* Γ₂) :
    Module.finrank k (Representation.tprod (ρ.comp e.toMonoidHom) σ).invariants =
      Module.finrank k (ρ.tprod (σ.comp e.symm.toMonoidHom)).invariants := by
  have hcomp : Representation.tprod (ρ.comp e.toMonoidHom) σ =
      (ρ.tprod (σ.comp e.symm.toMonoidHom)).comp e.toMonoidHom := by
    refine MonoidHom.ext fun q => ?_
    rw [MonoidHom.comp_apply, Representation.tprod_apply, Representation.tprod_apply]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rw [hcomp, invariants_comp_of_surjective _ _ e.surjective]

end Invariants

end Langlands.ProfiniteCohomology
