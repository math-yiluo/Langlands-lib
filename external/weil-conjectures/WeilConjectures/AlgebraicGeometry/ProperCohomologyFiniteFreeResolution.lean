/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

import WeilConjectures.RingTheory.PseudoCoherentBoundedFiniteFreeModel
import WeilConjectures.AlgebraicGeometry.AffineSheafResolutionOfRingModel
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Bounded flat complexes computing proper cohomology -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- An affine quasi-coherent complex with pseudo-coherent global sections admits an
actual finite-free resolution at its termwise upper bound.
Source: Stacks Project, Tag 064U, final assertion; Tags 01IB and 01HV.
Proof: Evaluation sends the zero terms above d to zero modules. Its resulting complex
therefore has zero cohomology above d. Apply the pseudo-coherent finite-free model theorem
at that bound. Every free term is projective, so the bounded-above model is K-projective.
Surjectivity of Qh on morphisms out of it lifts the derived isomorphism to a homotopy
class. Fullness of the homotopy quotient gives a chain map f. Naturality of the comparison
between Q and quotient followed by Qh shows Q(f) is the original derived isomorphism;
hence f is a quasi-isomorphism. Apply affine sheafification to P and f. This last step
uses exact tilde, the quasi-coherent counit and preservation of finite free modules.
No exactness of global sections is needed to establish the termwise upper bound.
(blueprint: lem-pc-proper-cohomology-finite-free-resolution). -/
theorem exists_proper_cohomology_finite_free_resolution {T : Scheme.{u}}
    (U : T.Opens) [IsAffine U.toScheme]
    (C : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (hCle : C.IsStrictlyLE d)
    (hCqc : ∀ n : ℤ, (C.X n).IsQuasicoherent)
    (hpc : (letI : CommRing (U.toScheme.ringCatSheaf.obj.obj (.op ⊤)) :=
        inferInstanceAs (CommRing Γ(U.toScheme, ⊤));
        letI := HasDerivedCategory.standard
          (ModuleCat.{u} (U.toScheme.ringCatSheaf.obj.obj (.op ⊤)));
        DerivedCategory.IsPseudoCoherent (DerivedCategory.Q.obj
          (((SheafOfModules.evaluation.{u} U.toScheme.ringCatSheaf (.op ⊤)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C)))) :
    ∃ Q : CochainComplex U.toScheme.Modules ℤ, Q.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ r : ℕ,
        Nonempty (Q.X n ≅ SheafOfModules.free
          (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))) ∧
      ∃ e : Q ⟶ C, QuasiIso e := by
  let R := U.toScheme.ringCatSheaf.obj.obj (.op ⊤)
  let : CommRing R := inferInstanceAs (CommRing Γ(U.toScheme, ⊤))
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let F := SheafOfModules.evaluation.{u} U.toScheme.ringCatSheaf (.op ⊤)
  let D : CochainComplex (ModuleCat.{u} R) ℤ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  have : C.IsStrictlyLE (d : ℤ) := hCle
  have hD : D.IsStrictlyLE (d : ℤ) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact F.map_isZero (C.isZero_of_isStrictlyLE d i hi)
  have hvan : ∀ i : ℤ, (d : ℤ) < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        (DerivedCategory.Q.obj D)) := by
    intro i hi
    exact (D.isZero_of_isLE d i hi).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app D)
  obtain ⟨P, hP, hfree, ⟨e⟩⟩ :=
    DerivedCategory.exists_finiteFree_model_isStrictlyLE
      (DerivedCategory.Q.obj D) d hpc hvan
  have : P.IsStrictlyLE (d : ℤ) := hP
  have (i : ℤ) : Projective (P.X i) := by
    have := (hfree i).1
    infer_instance
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P d
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient _ _).obj D)).surjective
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app P ≫ e.hom ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app D)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  have hf : DerivedCategory.Q.map f = e.hom := by
    have hn := DerivedCategory.quotientCompQhIso_hom_naturality f
    rw [hg] at hn
    apply (cancel_epi
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app P)).mp
    simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hn.symm
  have : IsIso (DerivedCategory.Q.map f) := by rw [hf]; infer_instance
  have : QuasiIso f :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{u} R) f).mp inferInstance
  exact exists_affine_sheaf_resolution_of_ring_model U C d hCqc P hP hfree f

end AlgebraicGeometry.Scheme.Modules
