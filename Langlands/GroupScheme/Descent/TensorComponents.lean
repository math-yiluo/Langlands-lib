import Langlands.GroupScheme.Descent.Data
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Algebra.Algebra.Pi

/-! # Actual scheme components from a finite tensor decomposition -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Descent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable {I : Type}

set_option backward.isDefEq.respectTransparency false in
/-- A finite spectrum decomposition with a small index and arbitrary ring universe. -/
theorem finiteSigmaSpec_isIso [Finite I] (R : I → CommRingCat.{u}) :
    IsIso (sigmaSpec R) := by
  let c : Fan R := Fan.mk (CommRingCat.of ((i : I) → R i))
    (fun i => CommRingCat.ofHom (Pi.evalRingHom _ i))
  have hc : IsLimit c :=
    { lift := fun s => CommRingCat.ofHom (RingHom.pi fun i => (s.π.app ⟨i⟩).hom)
      fac := by intros; rfl
      uniq := by
        intro s m h
        apply CommRingCat.hom_ext
        exact DFunLike.ext _ _ fun x => funext fun i =>
          DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (h ⟨i⟩)) x }
  have h : sigmaSpec R =
      (colimit.isoColimitCocone ⟨_,
        (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm _).symm
          (isColimitOfPreserves Scheme.Spec
            (Fan.IsLimit.op hc))⟩).hom := by
    ext i
    simp [c]
  rw [h]
  infer_instance

/-- The actual field-extension map of spectra. -/
abbrev fieldMap (k L : Type u) [Field k] [Field L] [Algebra k L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k L))

/-- A coordinate of a supplied finite tensor decomposition as an actual overlap map. -/
def tensorComponent (e : (L ⊗[k] L) ≃ₐ[L] (I → L)) (i : I) :
    Spec (CommRingCat.of L) ⟶ Overlap (fieldMap k L) :=
  Spec.map (CommRingCat.ofHom ((Pi.evalRingHom (fun _ : I => L) i).comp e.toRingHom)) ≫
    (pullbackSpecIso k L L).inv

/-- The supplied algebra equivalence gives an actual coproduct decomposition of the overlap. -/
instance tensorComponent_isIso_desc [Finite I] (e : (L ⊗[k] L) ≃ₐ[L] (I → L)) :
    IsIso (Sigma.desc (tensorComponent e)) := by
  have : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) :=
    isIso_SpecMap_iff.mpr e.bijective
  have : IsIso (sigmaSpec (fun _ : I => CommRingCat.of L)) := finiteSigmaSpec_isIso _
  have h : Sigma.desc (tensorComponent e) =
      sigmaSpec (fun _ : I => CommRingCat.of L) ≫
        Spec.map (CommRingCat.ofHom e.toRingHom) ≫ (pullbackSpecIso k L L).inv := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc, ι_sigmaSpec_assoc, tensorComponent]
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  rw [h]
  infer_instance

@[reassoc (attr := simp)]
theorem tensorComponent_fst (e : (L ⊗[k] L) ≃ₐ[L] (I → L)) (i : I) :
    tensorComponent e i ≫ fst (fieldMap k L) = 𝟙 _ := by
  dsimp only [tensorComponent, fst, fieldMap]
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  change e (a ⊗ₜ[k] 1) i = a
  have h := congrFun (e.commutes a) i
  exact h

/-- The pure-tensor formula identifies the other structural map with its specified automorphism. -/
@[reassoc (attr := simp)]
theorem tensorComponent_snd
    (e : (L ⊗[k] L) ≃ₐ[L] (I → L)) (s : I → L ≃ₐ[k] L)
    (he : ∀ a b i, e (a ⊗ₜ[k] b) i = a * s i b) (i : I) :
    tensorComponent e i ≫ snd (fieldMap k L) =
      Spec.map (CommRingCat.ofHom (s i).toRingHom) := by
  dsimp only [tensorComponent, snd, fieldMap]
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext b
  change e (1 ⊗ₜ[k] b) i = s i b
  simp only [he, one_mul]

instance tensorComponent_fst_isIso (e : (L ⊗[k] L) ≃ₐ[L] (I → L)) (i : I) :
    IsIso (tensorComponent e i ≫ fst (fieldMap k L)) := by
  rw [tensorComponent_fst]
  infer_instance

theorem tensorComponent_snd_isIso
    (e : (L ⊗[k] L) ≃ₐ[L] (I → L)) (s : I → L ≃ₐ[k] L)
    (he : ∀ a b i, e (a ⊗ₜ[k] b) i = a * s i b) (i : I) :
    IsIso (tensorComponent e i ≫ snd (fieldMap k L)) := by
  rw [tensorComponent_snd e s he]
  exact isIso_SpecMap_iff.mpr (s i).bijective

end Langlands.GroupScheme.Descent
