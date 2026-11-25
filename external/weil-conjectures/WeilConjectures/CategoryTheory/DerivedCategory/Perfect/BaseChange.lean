/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.RingTheory.TensorProduct.Finite
public import WeilConjectures.Algebra.Homology.FlatComplexBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Base change of perfect complexes

Let `K` be a bounded complex of flat modules over a commutative ring `A` whose image in `D(A)` is
perfect, and `B` an `A`-algebra. Then the base change `B ⊗[A] K`, which computes the derived base
change of `K`, is perfect in `D(B)` (`DerivedCategory.isPerfect_Q_obj_baseChange`).

A bounded complex `P` of finitely generated projective modules is K-projective, so an
isomorphism `P ≅ K` in `D(A)` comes from a quasi-isomorphism `P ⟶ K` of complexes. Its mapping
cone is a bounded acyclic complex of flat modules, which stays acyclic after base change; hence
`B ⊗[A] P ⟶ B ⊗[A] K` is a quasi-isomorphism, and `B ⊗[A] P` is a bounded complex of finitely
generated projective `B`-modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- An isomorphism `Q P ≅ Q K` in the derived category, with `P` K-projective, is induced by a
quasi-isomorphism `P ⟶ K`. -/
lemma exists_quasiIso_of_isKProjective {P K : CochainComplex C ℤ} [P.IsKProjective]
    (e : Q.obj P ≅ Q.obj K) : ∃ α : P ⟶ K, QuasiIso α := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient _ _).obj K)).surjective
    ((quotientCompQhIso C).hom.app P ≫ e.hom ≫ (quotientCompQhIso C).inv.app K)
  obtain ⟨α, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective g
  refine ⟨α, (isIso_Q_map_iff_quasiIso (C := C) α).1 ?_⟩
  have h := quotientCompQhIso_hom_naturality (C := C) α
  rw [hg] at h
  have : Q.map α = e.hom := by
    rw [← cancel_epi ((quotientCompQhIso C).hom.app P), ← h]
    simp
  rw [this]
  infer_instance

end DerivedCategory

namespace DerivedCategory

variable {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]

/-- **Base change of a perfect complex.** Let `K` be a bounded complex of flat `A`-modules whose
image in `D(A)` is perfect. Then for every `A`-algebra `B`, the image in `D(B)` of the base change
`B ⊗[A] K` is perfect. -/
theorem isPerfect_Q_obj_baseChange (K : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] (hK : ∀ i, Module.Flat A (K.X i))
    (hP : (Q.obj K).IsPerfect) :
    (Q.obj (((ModuleCat.baseChange A B).mapHomologicalComplex _).obj K)).IsPerfect := by
  obtain ⟨P, a', b', _, _, hPfin, ⟨e⟩⟩ := hP
  have : ∀ n, Projective (P.X n) := fun n ↦
    (IsProjective.iff_projective (P.X n)).1 (hPfin n).1
  have := CochainComplex.isKProjective_of_projective P b'
  obtain ⟨α, hα⟩ := exists_quasiIso_of_isKProjective e.symm
  have hPflat (i : ℤ) : Module.Flat A (P.X i) := by
    have := (hPfin i).1
    infer_instance
  -- the mapping cone of `α` vanishes in high degrees
  have hcone (k : ℤ) (hk : max b' b + 1 ≤ k) :
      Module.Flat A (LinearMap.ker ((CochainComplex.mappingCone α).d k (k + 1)).hom) := by
    have hz : IsZero ((CochainComplex.mappingCone α).X k) :=
      (CochainComplex.mappingCone.isZero_X_iff α k).2
        ⟨P.isZero_of_isStrictlyLE b' (k + 1) (by lia), K.isZero_of_isStrictlyLE b k (by lia)⟩
    have : Subsingleton ((CochainComplex.mappingCone α).X k) := ModuleCat.subsingleton_of_isZero hz
    infer_instance
  have hβ := CochainComplex.quasiIso_map_baseChange B α hPflat hK hcone
  let F := (ModuleCat.baseChange A B).mapHomologicalComplex (ComplexShape.up ℤ)
  have : CochainComplex.IsStrictlyGE (F.obj P) a' :=
    (CochainComplex.isStrictlyGE_iff _ a').2 fun i hi ↦
      (ModuleCat.baseChange A B).map_isZero (P.isZero_of_isStrictlyGE a' i hi)
  have : CochainComplex.IsStrictlyLE (F.obj P) b' :=
    (CochainComplex.isStrictlyLE_iff _ b').2 fun i hi ↦
      (ModuleCat.baseChange A B).map_isZero (P.isZero_of_isStrictlyLE b' i hi)
  refine (isPerfect_Q_obj (F.obj P) a' b' fun i ↦ ?_).of_iso (asIso (Q.map (F.map α)))
  have := (hPfin i).1
  have := (hPfin i).2
  exact ⟨inferInstanceAs (Module.Projective B (B ⊗[A] P.X i)),
    inferInstanceAs (Module.Finite B (B ⊗[A] P.X i))⟩

end DerivedCategory
