import Langlands.Cohomology.Profinite.Corestriction
import Langlands.Cohomology.Profinite.Cup.Functoriality

noncomputable section

namespace Langlands.ProfiniteCohomology

open CategoryTheory MonoidalCategory TensorProduct

universe u

variable {k G : Type u} [CommRing k] [Group G]

section Coind

variable (U : Subgroup G) (A B : Rep.{u} k G)

def coindTensorRightFun (f : Rep.coind U.subtype (Rep.res U.subtype A)) (b : B) :
    Rep.coind U.subtype (Rep.res U.subtype (A ⊗ B)) :=
  ⟨fun x => (f.1 x ⊗ₜ[k] B.ρ x b : (A ⊗ B : Rep k G)), fun u x => by
    change f.1 (U.subtype u * x) ⊗ₜ[k] B.ρ (U.subtype u * x) b =
      A.ρ (u : G) (f.1 x) ⊗ₜ[k] B.ρ (u : G) (B.ρ x b)
    rw [f.2 u x, map_mul, Module.End.mul_apply]
    rfl⟩

def coindTensorLeftFun (a : A) (f : Rep.coind U.subtype (Rep.res U.subtype B)) :
    Rep.coind U.subtype (Rep.res U.subtype (A ⊗ B)) :=
  ⟨fun x => (A.ρ x a ⊗ₜ[k] f.1 x : (A ⊗ B : Rep k G)), fun u x => by
    change A.ρ (U.subtype u * x) a ⊗ₜ[k] f.1 (U.subtype u * x) =
      A.ρ (u : G) (A.ρ x a) ⊗ₜ[k] B.ρ (u : G) (f.1 x)
    rw [f.2 u x, map_mul, Module.End.mul_apply]
    rfl⟩

def coindTensorRight :
    Rep.coind U.subtype (Rep.res U.subtype A) ⊗ B ⟶
      Rep.coind U.subtype (Rep.res U.subtype (A ⊗ B)) :=
  Rep.ofHom ⟨TensorProduct.lift (LinearMap.mk₂ k (coindTensorRightFun U A B)
      (fun f f' b => Subtype.ext (funext fun x => TensorProduct.add_tmul _ _ _))
      (fun c f b => Subtype.ext (funext fun x => (TensorProduct.smul_tmul' _ _ _).symm))
      (fun f b b' => Subtype.ext (funext fun x => by
        change f.1 x ⊗ₜ[k] B.ρ x (b + b') = f.1 x ⊗ₜ[k] B.ρ x b + f.1 x ⊗ₜ[k] B.ρ x b'
        rw [map_add, TensorProduct.tmul_add]))
      (fun c f b => Subtype.ext (funext fun x => by
        change f.1 x ⊗ₜ[k] B.ρ x (c • b) = c • (f.1 x ⊗ₜ[k] B.ρ x b)
        rw [map_smul, TensorProduct.tmul_smul]))),
    fun g => TensorProduct.ext' fun f b => Subtype.ext (funext fun x => by
      change f.1 (x * g) ⊗ₜ[k] B.ρ x (B.ρ g b) = f.1 (x * g) ⊗ₜ[k] B.ρ (x * g) b
      rw [map_mul, Module.End.mul_apply])⟩

def coindTensorLeft :
    A ⊗ Rep.coind U.subtype (Rep.res U.subtype B) ⟶
      Rep.coind U.subtype (Rep.res U.subtype (A ⊗ B)) :=
  Rep.ofHom ⟨TensorProduct.lift (LinearMap.mk₂ k (coindTensorLeftFun U A B)
      (fun a a' f => Subtype.ext (funext fun x => by
        change A.ρ x (a + a') ⊗ₜ[k] f.1 x = A.ρ x a ⊗ₜ[k] f.1 x + A.ρ x a' ⊗ₜ[k] f.1 x
        rw [map_add, TensorProduct.add_tmul]))
      (fun c a f => Subtype.ext (funext fun x => by
        change A.ρ x (c • a) ⊗ₜ[k] f.1 x = c • (A.ρ x a ⊗ₜ[k] f.1 x)
        rw [map_smul, TensorProduct.smul_tmul']))
      (fun a f f' => Subtype.ext (funext fun x => TensorProduct.tmul_add _ _ _))
      (fun c a f => Subtype.ext (funext fun x => TensorProduct.tmul_smul _ _ _))),
    fun g => TensorProduct.ext' fun a f => Subtype.ext (funext fun x => by
      change A.ρ x (A.ρ g a) ⊗ₜ[k] f.1 (x * g) = A.ρ (x * g) a ⊗ₜ[k] f.1 (x * g)
      rw [map_mul, Module.End.mul_apply])⟩

theorem coindTensorRight_comp_coindEvalOne :
    (Rep.resFunctor U.subtype).map (coindTensorRight U A B) ≫
        coindEvalOne U (Rep.res U.subtype (A ⊗ B)) =
      resTensorHom U.subtype (coindEvalOne U (Rep.res U.subtype A)) (𝟙 _) ≫
        (resTensorIso U.subtype A B).inv := by
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul f b =>
    change f.1 1 ⊗ₜ[k] B.ρ 1 b = f.1 1 ⊗ₜ[k] b
    rw [map_one, Module.End.one_apply]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

variable [U.FiniteIndex]


theorem coindTensorRight_comp_coindTrace :
    coindTensorRight U A B ≫ coindTrace U (A ⊗ B) = coindTrace U A ▷ B := by
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul f b =>
    change (coindTrace U (A ⊗ B)).hom ((coindTensorRight U A B).hom (f ⊗ₜ[k] b)) =
      (coindTrace U A).hom f ⊗ₜ[k] b
    rw [coindTrace_hom_apply, coindTrace_hom_apply, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun c _ => ?_
    change (A ⊗ B).ρ c.out (f.1 c.out⁻¹ ⊗ₜ[k] B.ρ c.out⁻¹ b) = A.ρ c.out (f.1 c.out⁻¹) ⊗ₜ[k] b
    rw [tensor_ρ_tmul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

end Coind

variable [TopologicalSpace G] [IsTopologicalGroup G]

section Composition

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →ₜ* G)
   {p : ℕ}

theorem map_coeffMap {A A' : Rep.{u} k G} {B : Rep.{u} k H} [IsSmoothRep A]
    [IsSmoothRep A'] [IsSmoothRep B] (f : A ⟶ A') (g : Rep.res φ A' ⟶ B)
    (w : cohomology A p) :
    map φ g p (coeffMap f p w) =
      map φ ((Rep.resFunctor (φ : H →* G)).map f ≫ g) p w := by
  induction w using cohomology_induction_on with | h w => ?_
  rw [cohomologyMap_cohomologyπ, map_cohomologyπ, map_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cocyclesMap, cochainOf_cocycleι_cocyclesMap,
    cochainOf_cocycleι_cyclesMap]
  rfl

theorem cohomologyMap_map {A : Rep.{u} k G} {B B' : Rep.{u} k H} [IsSmoothRep A]
    [IsSmoothRep B] [IsSmoothRep B'] (f : Rep.res φ A ⟶ B) (g : B ⟶ B')
    (w : cohomology A p) :
    coeffMap g p (map φ f p w) = map φ (f ≫ g) p w := by
  induction w using cohomology_induction_on with | h w => ?_
  rw [map_cohomologyπ, cohomologyMap_cohomologyπ, map_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesMap,
    cochainOf_cocycleι_cocyclesMap]
  rfl

end Composition

section Projection

variable [CompactSpace G] (U : OpenSubgroup G) {A B : Rep.{u} k G} [IsSmoothRep A]
  [IsSmoothRep B] {p q n : ℕ}

instance isSmoothRep_coind_res_tensor_right :
    IsSmoothRep (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A) ⊗ B) :=
  isSmoothRep_tensor _ _

theorem shapiroMap_inv_apply {C : Rep.{u} k (U : Subgroup G)} [IsSmoothRep C] (m : ℕ)
    (w : cohomology C m) : shapiroMap U C m (inv (shapiroMap U C m) w) = w :=
  ConcreteCategory.congr_hom (IsIso.inv_hom_id (shapiroMap U C m)) w

theorem inv_shapiroMap_apply {C : Rep.{u} k (U : Subgroup G)} [IsSmoothRep C] (m : ℕ)
    (w : cohomology (Rep.coind (U : Subgroup G).subtype C) m) :
    inv (shapiroMap U C m) (shapiroMap U C m w) = w :=
  ConcreteCategory.congr_hom (IsIso.hom_inv_id (shapiroMap U C m)) w

theorem cores_shapiroMap (A : Rep.{u} k G) [IsSmoothRep A]
    (w : cohomology (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) p) :
    cores U A p (shapiroMap U (Rep.res (U : Subgroup G).subtype A) p w) =
      coeffMap (coindTrace (U : Subgroup G) A) p w := by
  rw [cores, ConcreteCategory.comp_apply, inv_shapiroMap_apply]

theorem cores_cup_res (h : p + q = n)
    (x : cohomology (Rep.res (U : Subgroup G).subtype A) p) (y : cohomology B q) :
    cores U (A ⊗ B) n (coeffMap (resTensorIso (U : Subgroup G).subtype A B).inv n
        (cup h x (res B U q y))) =
      cup h (cores U A p x) y := by
  obtain ⟨z, rfl⟩ : ∃ z, shapiroMap U (Rep.res (U : Subgroup G).subtype A) p z = x :=
    ⟨_, shapiroMap_inv_apply U p x⟩
  have hkey : coeffMap (resTensorIso (U : Subgroup G).subtype A B).inv n
      (cup h (shapiroMap U (Rep.res (U : Subgroup G).subtype A) p z) (res B U q y)) =
        shapiroMap U (Rep.res (U : Subgroup G).subtype (A ⊗ B)) n
          (coeffMap (coindTensorRight (U : Subgroup G) A B) n (cup h z y)) := by
    rw [shapiroMap_eq, shapiroMap_eq, res_eq, ← map_resTensorHom_cup,
      cohomologyMap_map, map_coeffMap]
    erw [coindTensorRight_comp_coindEvalOne]
    rfl
  rw [hkey, cores_shapiroMap, cores_shapiroMap, ← ConcreteCategory.comp_apply,
    ← coeffMap_comp, coindTensorRight_comp_coindTrace, cohomologyMap_whiskerRight_cup]

end Projection

end Langlands.ProfiniteCohomology
