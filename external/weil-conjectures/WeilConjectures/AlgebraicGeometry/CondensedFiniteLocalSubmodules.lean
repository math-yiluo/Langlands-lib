/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFamilyHomDescent

/-!
# Descending compatible local submodules to one finite coefficient field

Source: upstream ModuleObject/Colimit/TwoColimit.lean, (Obj) overlap descent paragraph
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private lemma iso_of_overlap_maps
    {C : Type*} [Category C] {A B P Q : C} (a : A ⟶ P) (b : B ⟶ Q)
    [Mono a] [Mono b] (e : P ≅ Q) (s : A ⟶ B) (t : B ⟶ A)
    (hs : s ≫ b = a ≫ e.hom) (ht : t ≫ a = b ≫ e.inv) :
    ∃ c : A ≅ B, c.hom ≫ b = a ≫ e.hom := by
  refine ⟨⟨s, t, ?_, ?_⟩, hs⟩
  · apply (cancel_mono a).mp
    rw [Category.assoc, ht, ← Category.assoc, hs, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · apply (cancel_mono b).mp
    rw [Category.assoc, hs, ← Category.assoc, ht, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- After a finite enlargement, the adjoints of the local model isomorphisms
are compatible embeddings into the restriction of the given module.

Source: upstream ModuleObject/Colimit/TwoColimit.lean, (Obj) overlap descent paragraph.
(auxiliary; not a blueprint node).

Proof: choose the supplied local isomorphisms. At every finite stage construct the
canonical scalar adjoints using tensor transitivity and the extension adjunction.
The coefficient-linear projection from the algebraic closure splits the extension
unit after all inverse images, so the adjoints are monic. Their scalar adjuncts are
the chosen local isomorphisms composed with tensor-transitivity isomorphisms.
Pairwise overlaps are qcqs because X is quasi-separated and the covering schemes
are affine. Apply Hom descent to the finite family of all ordered pairs, using each overlap
in both directions. This gives a common
finite F and forward and reverse maps commuting with the canonical adjoints.
The reverse upperStarCompIso is the inverse of the forward comparison. Compose
the two equations and cancel the pulled monomorphisms to prove that the maps are
mutual inverses. Thus they form the required underlying overlap isomorphisms, and
the forward equations give their compatibility. No further field enlargement or
eventual-equality argument is needed for these inverse identities. The empty cover
is covered by the empty-family case, with F = E. -/
theorem exists_finiteCoefficient_compatible_local_monomorphisms
    (T X : Scheme.{u}) [QuasiSeparatedSpace X]
    (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hfinite : Finite U.I₀) (haffine : ∀ i, IsAffine (U.X i))
    (N : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
      ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))
    (hN : ∀ i, Mod.IsFinitelyPresented
      ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))) (N i))
    (e : ∀ i, Nonempty ((Mod.extendScalars
      ((upperStar Ab.{u + 1} (U.f i)).map
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj
          (N i) ≅
      ((upperStar Ab.{u + 1} (U.f i)).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)) :
    ∃ (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F),
      let R := (upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F)
      let S := (upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)
      let a := (upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ F)
      let L := fun i ↦ (Mod.extendScalars ((upperStar Ab.{u + 1} (U.f i)).map
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)))).obj (N i)
      ∃ q : ∀ i, L i ⟶ ((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj
        ((Mod.comap a).obj M),
        (∀ i, Mono (q i)) ∧
        (∀ i, IsIso (((Mod.extendRestrictAdjunction
          ((upperStar Ab.{u + 1} (U.f i)).map a)).homEquiv (L i)
            (((upperStar Ab.{u + 1} (U.f i)).mapMod S).obj M)).symm
              (q i ≫ ((upperStar Ab.{u + 1} (U.f i)).mapModComapIso a).hom.app M))) ∧
        (∀ i j, ∃ c :
          (upperStar Ab.{u + 1} (pullback.fst (U.f i) (U.f j))).obj (L i).X ≅
            (upperStar Ab.{u + 1} (pullback.snd (U.f i) (U.f j))).obj (L j).X,
          c.hom ≫ (upperStar Ab.{u + 1} (pullback.snd (U.f i) (U.f j))).map (q j).hom =
            (upperStar Ab.{u + 1} (pullback.fst (U.f i) (U.f j))).map (q i).hom ≫
              (upperStarCompIso Ab.{u + 1}
                (pullback.condition (f := U.f i) (g := U.f j))).hom.app
                  ((Mod.comap a).obj M).X) := by
  classical
  let ei := fun i ↦ Classical.choice (e i)
  let q (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F) :=
    fun i ↦ finiteCoefficientLocalAdjoint T X f ℓ E (U.X i) (U.f i) (N i) M
      (ei i).hom F hEF
  have hmono (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F)
      (i : U.I₀) : Mono (q F hEF i) :=
    mono_finiteCoefficientLocalAdjoint T X f ℓ E (U.X i) (U.f i) (N i) M
      (ei i).hom F hEF
  let : Finite U.I₀ := hfinite
  let : ∀ i : U.I₀, IsAffine (U.X i) := haffine
  let : ∀ (i j : U.I₀), CompactSpace (pullback (U.f i) (U.f j) : Scheme.{u}) := by
    intro i j
    infer_instance
  let : ∀ (i j : U.I₀), QuasiSeparatedSpace (pullback (U.f i) (U.f j) : Scheme.{u}) := by
    intro i j
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd (U.f i) (U.f j))
  obtain ⟨F, hEF, hfac⟩ := exists_finiteCoefficient_family_hom_factorizations
    T X f ℓ M E U.I₀ U.X U.f N hN ei
  refine ⟨F, hEF, q F hEF, hmono F hEF, ?_, ?_⟩
  · intro i
    dsimp only [q]
    erw [finiteCoefficientLocalAdjoint_scalarAdjoint T X f ℓ E (U.X i) (U.f i)
      (N i) M (ei i).hom F hEF]
    exact isIso_finiteCoefficientLocalTensorMap T X f ℓ E (U.X i) (U.f i) (N i) M
      (ei i).hom F hEF
  · intro i j
    obtain ⟨s, t, hs, ht⟩ := hfac i j
    let : ∀ i : U.I₀, Mono (q F hEF i).hom := by
      intro i
      have := hmono F hEF i
      exact (Mod.forget _).map_mono (q F hEF i)
    exact iso_of_overlap_maps
      ((upperStar Ab.{u + 1} (pullback.fst (U.f i) (U.f j))).map (q F hEF i).hom)
      ((upperStar Ab.{u + 1} (pullback.snd (U.f i) (U.f j))).map (q F hEF j).hom)
      ((upperStarCompIso Ab.{u + 1}
        (pullback.condition (f := U.f i) (g := U.f j))).app
          ((Mod.comap ((upperStar Ab.{u + 1} f).map
            (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj M).X) s t hs ht

end AlgebraicGeometry.ProEtale
