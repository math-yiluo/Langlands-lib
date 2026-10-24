import Langlands.Cohomology.Tate.OrdinaryCupStatement
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

noncomputable section

universe u

open CategoryTheory groupCohomology

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G]

lemma ordinaryClass_invariant (A : Rep.{u} R G) (a : A.ρ.invariants) :
    π A 0 ((cocyclesIso₀ A).inv a) = (H0Iso A).inv a := by
  have hp : (H0Iso A).hom (π A 0 ((cocyclesIso₀ A).inv a)) = a :=
    (ConcreteCategory.congr_hom (π_comp_H0Iso_hom A) _).trans
      (ConcreteCategory.congr_hom (cocyclesIso₀ A).inv_hom_id a)
  exact (H0Iso A).toLinearEquiv.injective
    (hp.trans (ConcreteCategory.congr_hom (H0Iso A).inv_hom_id a).symm)

lemma ordinaryCup_zero_invariant {A B C : Rep.{u} R G} (φ : Pairing A B C)
    (a : A.ρ.invariants) (b : B.ρ.invariants) :
    ordinaryCup φ 0 0 ((H0Iso A).inv a) ((H0Iso B).inv b) =
      (H0Iso C).inv (φ.onInvariants a b) := by
  rw [← ordinaryClass_invariant A, ← ordinaryClass_invariant B,
    ordinaryCup_π_π, ← ordinaryClass_invariant C]
  congr 1
  apply OrdinaryCup.cocycle_ext
  funext x
  rw [ordinaryCupCocycles_apply]
  simp [cocyclesIso₀_inv_comp_iCocycles_apply, cochainsIso₀, Pairing.onInvariants]
  rfl

lemma iCocycles_coefficientMap {A B : Rep.{u} R G} (f : A ⟶ B) (n : ℕ)
    (a : cocycles A n) (x : Fin n → G) :
    iCocycles B n (cocyclesMap (MonoidHom.id G) f n a) x =
      f.hom (iCocycles A n a x) := by
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (cochainsMap (MonoidHom.id G) f) n) a
  exact congrFun h x

lemma ordinaryCupCocycles_naturality {A A' B B' C C' : Rep.{u} R G}
    (φ : Pairing A B C) (φ' : Pairing A' B' C')
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C')
    (hφ : ∀ a b, h.hom (φ.bilinear a b) = φ'.bilinear (f.hom a) (g.hom b))
    (p q : ℕ) (a : cocycles A p) (b : cocycles B q) :
    cocyclesMap (MonoidHom.id G) h (p + q) (ordinaryCupCocycles φ p q a b) =
      ordinaryCupCocycles φ' p q (cocyclesMap (MonoidHom.id G) f p a)
        (cocyclesMap (MonoidHom.id G) g q b) := by
  apply OrdinaryCup.cocycle_ext
  funext x
  calc
    _ = h.hom (iCocycles C (p + q) (ordinaryCupCocycles φ p q a b) x) :=
      iCocycles_coefficientMap h (p + q) _ x
    _ = h.hom (φ.bilinear (iCocycles A p a (fun i => x (Fin.castAdd q i)))
        (B.ρ (List.ofFn fun i : Fin p => x (Fin.castAdd q i)).prod
          (iCocycles B q b (fun j => x (Fin.natAdd p j))))) :=
      congrArg h.hom (ordinaryCupCocycles_apply φ p q a b x)
    _ = _ := by
      rw [hφ, Rep.hom_comm_apply]
      exact (congrArg₂ (fun a b => φ'.bilinear a b)
        (iCocycles_coefficientMap f p a _).symm
        (congrArg (B'.ρ _) (iCocycles_coefficientMap g q b _).symm)).trans
          (ordinaryCupCocycles_apply φ' p q _ _ x).symm

lemma ordinaryCup_naturality {A A' B B' C C' : Rep.{u} R G}
    (φ : Pairing A B C) (φ' : Pairing A' B' C')
    (f : A ⟶ A') (g : B ⟶ B') (h : C ⟶ C')
    (hφ : ∀ a b, h.hom (φ.bilinear a b) = φ'.bilinear (f.hom a) (g.hom b))
    (p q : ℕ) (a : groupCohomology A p) (b : groupCohomology B q) :
    groupCohomology.map (MonoidHom.id G) h (p + q) (ordinaryCup φ p q a b) =
      ordinaryCup φ' p q (groupCohomology.map (MonoidHom.id G) f p a)
        (groupCohomology.map (MonoidHom.id G) g q b) := by
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (π A p)).mp inferInstance a
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective (π B q)).mp inferInstance b
  rw [ordinaryCup_π_π, π_map_apply, π_map_apply, π_map_apply, ordinaryCup_π_π]
  congr 1
  exact ordinaryCupCocycles_naturality φ φ' f g h hφ p q a b

/-- Exact normalization and naturality laws for the actual ordinary cochain cup. -/
theorem ordinaryCupLaws : OrdinaryCupLaws.{u} := by
  intro R G _ _
  exact ⟨fun A B C φ a b => ordinaryCup_zero_invariant φ a b,
    fun A A' B B' C C' φ φ' f g h hφ p q a b =>
      ordinaryCup_naturality φ φ' f g h hφ p q a b⟩

end Langlands.Tate
