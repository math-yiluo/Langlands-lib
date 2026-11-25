/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses

/-!
# Tensor descent through sheafification in independent universes

Source: Stacks Project, Modules on Sites, Tags 03EK and 05V4.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Opposite
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {P Q G : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)
  [Presheaf.IsLocallyInjective J f] [Presheaf.IsLocallySurjective J f]
  (hG : Presieve.IsSheaf J G) (g : P ⟶ G)

omit [Presheaf.IsLocallySurjective J f] in
include hG in
private theorem eq_of_local_image_eq {U : Cᵒᵖ} (x y : P.obj U)
    (h : f.app U x = f.app U y) : g.app U x = g.app U y := by
  apply (hG.isSeparated _ (Presheaf.equalizerSieve_mem J f x y h)).ext
  intro V i hi
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hi]

include hG in
private theorem existsUnique_local_lift (U : Cᵒᵖ) (q : Q.obj U) :
    ∃! t : G.obj U, ∀ (V : C) (i : V ⟶ U.unop) (p : P.obj (op V)),
      f.app (op V) p = Q.map i.op q → G.map i.op t = g.app (op V) p := by
  let S := Presheaf.imageSieve f q
  have hS : S ∈ J U.unop := Presheaf.imageSieve_mem J f q
  let x : S.arrows.FamilyOfElements G :=
    fun V i hi ↦ g.app (op V) (Presheaf.localPreimage f q i hi)
  have hx : x.Compatible := by
    intro V₁ V₂ W i₁ i₂ j₁ j₂ hj₁ hj₂ hij
    dsimp [x]
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    apply eq_of_local_image_eq f hG g
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply,
      Presheaf.app_localPreimage, Presheaf.app_localPreimage,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hij]
  obtain ⟨t, ht, htuniq⟩ := hG _ hS x hx
  refine ⟨t, ?_, ?_⟩
  · intro V i p hp
    have hi : S i := ⟨p, hp⟩
    exact (ht i hi).trans (eq_of_local_image_eq f hG g _ _
      ((Presheaf.app_localPreimage f q i hi).trans hp.symm))
  · intro t' ht'
    apply htuniq
    intro V i hi
    exact ht' V i _ (Presheaf.app_localPreimage f q i hi)

private noncomputable def localLift : Q ⟶ G where
  app U := ↾fun q ↦ (existsUnique_local_lift f hG g U q).choose
  naturality {U V} i := by
    ext q
    apply (existsUnique_local_lift f hG g V (Q.map i q)).unique
    · exact (existsUnique_local_lift f hG g V (Q.map i q)).choose_spec.1
    · intro W j p hp
      change G.map j.op (G.map i _) = _
      rw [← Functor.map_comp_apply]
      exact (existsUnique_local_lift f hG g U q).choose_spec.1 W
        (j ≫ i.unop) p (by
          simpa only [op_comp, Functor.map_comp_apply, Quiver.Hom.op_unop] using hp)

include hG in
private theorem localLift_fac : f ≫ localLift f hG g = g := by
  ext U p
  have h := (existsUnique_local_lift f hG g U (f.app U p)).choose_spec.1
    U.unop (𝟙 _) p (by simp)
  simpa [localLift] using h

/-- Local bijectivity is sufficient for descent of maps to sheaves of sets,
without requiring the site universes to fit the value universe. -/
private theorem type_W_of_local_bijective : J.W f := by
  intro G hG
  have hG' := (isSheaf_iff_isSheaf_of_type J G).mp hG
  constructor
  · intro a b h
    ext U q
    apply (hG'.isSeparated _ (Presheaf.imageSieve_mem J f q)).ext
    intro V i hi
    obtain ⟨p, hp⟩ := hi
    change G.map i.op (a.app U q) = G.map i.op (b.app U q)
    rw [← NatTrans.naturality_apply a i.op, ← NatTrans.naturality_apply b i.op, ← hp]
    exact congrArg (fun t ↦ t.app (op V) p) h
  · intro g
    exact ⟨localLift f hG' g, localLift_fac f hG' g⟩
end CategoryTheory

namespace CategoryTheory
variable {C : Type u} [Category.{v} C]

private def sectionPairs (P N : Cᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Type w where
  obj U := P.obj U × N.obj U
  map i := ↾fun x ↦ (P.map i x.1, N.map i x.2)
  map_id U := by ext x <;> simp
  map_comp i j := by ext x <;> simp

private def sectionPairsMap {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)
    (N : Cᵒᵖ ⥤ Type w) : sectionPairs P N ⟶ sectionPairs Q N where
  app U := ↾fun x ↦ (f.app U x.1, x.2)
  naturality {U V} i := by ext x; simp [sectionPairs, NatTrans.naturality_apply]

private theorem sectionPairsMap_locallyInjective
    {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)
    [Presheaf.IsLocallyInjective J f] (N : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective J (sectionPairsMap f N) where
  equalizerSieve_mem {U} x y h := by
    change (f.app U x.1, x.2) = (f.app U y.1, y.2) at h
    have hp : f.app U x.1 = f.app U y.1 := congrArg (fun z : Q.obj U × N.obj U ↦ z.1) h
    have hn : x.2 = y.2 := congrArg (fun z : Q.obj U × N.obj U ↦ z.2) h
    apply J.superset_covering _ (Presheaf.equalizerSieve_mem J f x.1 y.1 hp)
    intro V i hi
    change (P.map i.op x.1, N.map i.op x.2) = (P.map i.op y.1, N.map i.op y.2)
    exact Prod.ext hi (congrArg (N.map i.op) hn)

private theorem sectionPairsMap_locallySurjective
    {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)
    [Presheaf.IsLocallySurjective J f] (N : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective J (sectionPairsMap f N) where
  imageSieve_mem {U} x := by
    apply J.superset_covering _ (Presheaf.imageSieve_mem J f x.1)
    intro V i hi
    obtain ⟨p, hp⟩ := hi
    exact ⟨(p, N.map i.op x.2), Prod.ext hp rfl⟩

private theorem sectionPairsMap_W
    {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)
    [Presheaf.IsLocallyInjective J f] [Presheaf.IsLocallySurjective J f]
    (N : Cᵒᵖ ⥤ Type w) : J.W (sectionPairsMap f N) := by
  have := sectionPairsMap_locallyInjective (J := J) f N
  have := sectionPairsMap_locallySurjective (J := J) f N
  exact type_W_of_local_bijective _
end CategoryTheory

namespace PresheafOfModules
universe r
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Cᵒᵖ ⥤ CommRingCat.{r}}
  {P Q N H : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)}

private noncomputable def underlyingPairs (P N : PresheafOfModules.{w}
    (R ⋙ forget₂ CommRingCat RingCat)) : Cᵒᵖ ⥤ Type w :=
  CategoryTheory.sectionPairs (P.presheaf ⋙ forget _) (N.presheaf ⋙ forget _)

private noncomputable def tensorPairing (g : SheafOfModules.siteTensorPresheaf P N ⟶ H) :
    underlyingPairs P N ⟶ H.presheaf ⋙ forget _ where
  app U := ↾fun x ↦ g.app U (x.1 ⊗ₜ[R.obj U] x.2)
  naturality {U V} i := by
    ext x
    exact naturality_apply g i (x.1 ⊗ₜ[R.obj U] x.2)

variable (f : P ⟶ Q) [IsLocallyInjective J f] [IsLocallySurjective J f]
  (hH : Presheaf.IsSheaf J H.presheaf)
  (g : SheafOfModules.siteTensorPresheaf P N ⟶ H)

private noncomputable def liftedPairing : underlyingPairs Q N ⟶ H.presheaf ⋙ forget _ :=
  ((CategoryTheory.sectionPairsMap_W (J := J)
    (Functor.whiskerRight ((toPresheaf _).map f) (forget _))
    (N.presheaf ⋙ forget _)).homEquiv _
      ((sheafCompose J (forget AddCommGrpCat.{w})).obj ⟨H.presheaf, hH⟩).property).symm
        (tensorPairing g)

private theorem liftedPairing_fac (U : Cᵒᵖ) (p : P.obj U) (n : N.obj U) :
    (liftedPairing f hH g).app U (f.app U p, n) = g.app U (p ⊗ₜ[R.obj U] n) := by
  have h := ((CategoryTheory.sectionPairsMap_W (J := J)
    (Functor.whiskerRight ((toPresheaf _).map f) (forget _))
    (N.presheaf ⋙ forget _)).homEquiv _
      ((sheafCompose J (forget AddCommGrpCat.{w})).obj ⟨H.presheaf, hH⟩).property).apply_symm_apply
        (tensorPairing g)
  exact congrArg (fun t ↦ t.app U (p, n)) h

private theorem liftedPairing_naturality {U V : Cᵒᵖ} (i : U ⟶ V)
    (q : Q.obj U) (n : N.obj U) :
    (liftedPairing f hH g).app V (Q.map i q, N.map i n) =
      H.map i ((liftedPairing f hH g).app U (q, n)) :=
  by
    have h := (liftedPairing f hH g).naturality i
    exact congrArg (fun k : (underlyingPairs Q N).obj U ⟶
      (H.presheaf ⋙ forget _).obj V ↦ k (q, n)) h

private theorem liftedPairing_add_left (U : Cᵒᵖ) (q q' : Q.obj U) (n : N.obj U) :
    (liftedPairing f hH g).app U (q + q', n) =
      (liftedPairing f hH g).app U (q, n) +
        (liftedPairing f hH g).app U (q', n) := by
  apply hH.isSeparated _ _
    (J.intersection_covering (Presheaf.imageSieve_mem J ((toPresheaf _).map f) q)
      (Presheaf.imageSieve_mem J ((toPresheaf _).map f) q'))
  intro V i hi
  obtain ⟨p, hp⟩ := hi.1
  obtain ⟨p', hp'⟩ := hi.2
  change f.app (op V) p = Q.map i.op q at hp
  change f.app (op V) p' = Q.map i.op q' at hp'
  change H.map i.op _ = H.map i.op (_ + _)
  rw [map_add, ← liftedPairing_naturality f hH g, ← liftedPairing_naturality f hH g,
    ← liftedPairing_naturality f hH g]
  erw [map_add, ← hp, ← hp', ← map_add]
  exact (liftedPairing_fac f hH g (op V) (p + p') (N.map i.op n)).trans
    (by
      rw [TensorProduct.add_tmul, map_add]
      exact congrArg₂ (· + ·)
        (liftedPairing_fac f hH g (op V) p (N.map i.op n)).symm
        (liftedPairing_fac f hH g (op V) p' (N.map i.op n)).symm)

private theorem liftedPairing_add_right (U : Cᵒᵖ) (q : Q.obj U) (n n' : N.obj U) :
    (liftedPairing f hH g).app U (q, n + n') =
      (liftedPairing f hH g).app U (q, n) +
        (liftedPairing f hH g).app U (q, n') := by
  apply hH.isSeparated _ _ (Presheaf.imageSieve_mem J ((toPresheaf _).map f) q)
  intro V i hi
  change ∃ p : P.obj (op V), f.app (op V) p = Q.map i.op q at hi
  obtain ⟨p, hp⟩ := hi
  change H.map i.op _ = H.map i.op (_ + _)
  rw [map_add, ← liftedPairing_naturality f hH g, ← liftedPairing_naturality f hH g,
    ← liftedPairing_naturality f hH g]
  erw [map_add, ← hp]
  exact (liftedPairing_fac f hH g (op V) p (N.map i.op n + N.map i.op n')).trans
    (by
      rw [TensorProduct.tmul_add, map_add]
      exact congrArg₂ (· + ·)
        (liftedPairing_fac f hH g (op V) p (N.map i.op n)).symm
        (liftedPairing_fac f hH g (op V) p (N.map i.op n')).symm)

private theorem liftedPairing_smul_left (U : Cᵒᵖ) (a : R.obj U)
    (q : Q.obj U) (n : N.obj U) :
    (liftedPairing f hH g).app U (a • q, n) =
      @SMul.smul (R.obj U) (H.obj U) inferInstance a
        ((liftedPairing f hH g).app U (q, n)) := by
  apply hH.isSeparated _ _ (Presheaf.imageSieve_mem J ((toPresheaf _).map f) q)
  intro V i hi
  change ∃ p : P.obj (op V), f.app (op V) p = Q.map i.op q at hi
  obtain ⟨p, hp⟩ := hi
  change H.map i.op _ = H.map i.op
    (@SMul.smul (R.obj U) (H.obj U) inferInstance a
      ((liftedPairing f hH g).app U (q, n)))
  erw [H.map_smul, ← liftedPairing_naturality f hH g,
    ← liftedPairing_naturality f hH g]
  erw [Q.map_smul]
  erw [← hp, ← map_smul]
  exact (liftedPairing_fac f hH g (op V) ((R.map i.op a) • p) (N.map i.op n)).trans
    (by
      erw [← TensorProduct.smul_tmul', map_smul]
      exact congrArg (fun t : H.obj (op V) ↦ (R.map i.op a) • t)
        (liftedPairing_fac f hH g (op V) p (N.map i.op n)).symm)

private theorem liftedPairing_smul_right (U : Cᵒᵖ) (a : R.obj U)
    (q : Q.obj U) (n : N.obj U) :
    (liftedPairing f hH g).app U (q, a • n) =
      @SMul.smul (R.obj U) (H.obj U) inferInstance a
        ((liftedPairing f hH g).app U (q, n)) := by
  apply hH.isSeparated _ _ (Presheaf.imageSieve_mem J ((toPresheaf _).map f) q)
  intro V i hi
  change ∃ p : P.obj (op V), f.app (op V) p = Q.map i.op q at hi
  obtain ⟨p, hp⟩ := hi
  change H.map i.op _ = H.map i.op
    (@SMul.smul (R.obj U) (H.obj U) inferInstance a
      ((liftedPairing f hH g).app U (q, n)))
  erw [H.map_smul, ← liftedPairing_naturality f hH g,
    ← liftedPairing_naturality f hH g]
  erw [N.map_smul]
  erw [← hp]
  exact (liftedPairing_fac f hH g (op V) p
    ((R.map i.op a) • N.restrictₛₗ i.op n)).trans
    (by
      rw [TensorProduct.tmul_smul, map_smul]
      exact congrArg (fun t : H.obj (op V) ↦ (R.map i.op a) • t)
        (liftedPairing_fac f hH g (op V) p (N.map i.op n)).symm)

private noncomputable def liftedBilinear (U : Cᵒᵖ) :
    Q.obj U →ₗ[R.obj U] N.obj U →ₗ[R.obj U] H.obj U where
  toFun q :=
    { toFun := fun n ↦ (liftedPairing f hH g).app U (q, n)
      map_add' := liftedPairing_add_right f hH g U q
      map_smul' := fun a n ↦ liftedPairing_smul_right f hH g U a q n }
  map_add' q q' := LinearMap.ext (liftedPairing_add_left f hH g U q q')
  map_smul' a q := LinearMap.ext (liftedPairing_smul_left f hH g U a q)

private noncomputable def tensorDesc : SheafOfModules.siteTensorPresheaf Q N ⟶ H where
  app U := ModuleCat.ofHom (TensorProduct.lift (liftedBilinear f hH g U))
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro q n
    exact liftedPairing_naturality f hH g i q n

private theorem tensorDesc_fac :
    SheafOfModules.siteTensorHom f N ≫ tensorDesc f hH g = g := by
  apply hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro p n
  exact liftedPairing_fac f hH g U p n

omit [IsLocallyInjective J f] in
include hH in
private theorem tensor_precomp_injective
    (a b : SheafOfModules.siteTensorPresheaf Q N ⟶ H)
    (h : SheafOfModules.siteTensorHom f N ≫ a =
      SheafOfModules.siteTensorHom f N ≫ b) : a = b := by
  apply hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro q n
  apply hH.isSeparated _ _ (Presheaf.imageSieve_mem J ((toPresheaf _).map f) q)
  intro V i hi
  change ∃ p : P.obj (op V), f.app (op V) p = Q.map i.op q at hi
  obtain ⟨p, hp⟩ := hi
  change H.map i.op (a.app U (q ⊗ₜ[R.obj U] n)) =
    H.map i.op (b.app U (q ⊗ₜ[R.obj U] n))
  calc
    _ = a.app (op V) (Q.map i.op q ⊗ₜ[R.obj (op V)] N.map i.op n) :=
      (naturality_apply a i.op (q ⊗ₜ[R.obj U] n)).symm
    _ = b.app (op V) (Q.map i.op q ⊗ₜ[R.obj (op V)] N.map i.op n) := by
      rw [← hp]
      exact congrArg (fun k ↦ k.app (op V) (p ⊗ₜ[R.obj (op V)] N.map i.op n)) h
    _ = _ := naturality_apply b i.op (q ⊗ₜ[R.obj U] n)

omit hH g in
/-- Tensoring a locally bijective module map becomes an isomorphism after sheafification.
Source: Stacks Project, Modules on Sites, Tag 03EK and Tag 05V4
(auxiliary; not a blueprint node).
Proof: a bilinear map out of the source tensor product descends uniquely to the target:
locally lift the first operand, apply the original pairing, and glue in the target sheaf.
Local injectivity makes this independent of the lifts. Additivity and homogeneity can
be checked on the covering sieves where lifts exist. The tensor universal property and
sheafification adjunction therefore give bijections on maps to every module sheaf.
The sheafified tensor map is consequently an isomorphism. -/
theorem sheafification_tensorHom_isIso
    (hR : Presheaf.IsSheaf J (R ⋙ forget₂ CommRingCat RingCat))
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{w}] :
    IsIso ((sheafification (R := ⟨_, hR⟩) (𝟙 (R ⋙ forget₂ CommRingCat RingCat))).map
      (SheafOfModules.siteTensorHom f N)) := by
  let L := sheafification (R := ⟨_, hR⟩) (𝟙 (R ⋙ forget₂ CommRingCat RingCat))
  let adj := sheafificationAdjunction (R := ⟨_, hR⟩) (𝟙 (R ⋙ forget₂ CommRingCat RingCat))
  apply isIso_of_coyoneda_map_bijective
  intro T
  let eP := adj.homEquiv (SheafOfModules.siteTensorPresheaf P N) T
  let eQ := adj.homEquiv (SheafOfModules.siteTensorPresheaf Q N) T
  have fac (k : L.obj (SheafOfModules.siteTensorPresheaf Q N) ⟶ T) :
      eP (L.map (SheafOfModules.siteTensorHom f N) ≫ k) =
        SheafOfModules.siteTensorHom f N ≫ eQ k :=
    adj.homEquiv_naturality_left _ k
  constructor
  · intro a b hab
    apply eQ.injective
    apply tensor_precomp_injective
      (H := (restrictScalars (𝟙 (R ⋙ forget₂ CommRingCat RingCat))).obj T.val) f T.isSheaf
    exact (fac a).symm.trans ((congrArg eP hab).trans (fac b))
  · intro k
    let g := tensorDesc
      (H := (restrictScalars (𝟙 (R ⋙ forget₂ CommRingCat RingCat))).obj T.val)
      f T.isSheaf (eP k)
    refine ⟨eQ.symm g, eP.injective ?_⟩
    rw [fac, Equiv.apply_symm_apply]
    exact tensorDesc_fac f T.isSheaf (eP k)

end PresheafOfModules
