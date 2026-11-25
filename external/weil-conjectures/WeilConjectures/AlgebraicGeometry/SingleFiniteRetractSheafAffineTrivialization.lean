/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.MorphismProperty.Retract
import WeilConjectures.RingTheory.FiniteProjectivePrimeLocalFree
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Affine trivialization of a single finite free retract

Source: Stacks Project, Tags 00NX, 01IA and 01IB.
(blueprint: new-pc-single-retract-sheaf-affine-trivialization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Sections preserve the splitting. The affine counit is a retract of the counit on
finite free sheaves, hence invertible. The sections of the ambient sheaf are finite free
by `tildeFinsupp` and the unit of tilde-Gamma, so its summand is finite projective.
Source: Stacks Project, Tags 01IA, 01IB and 00NX. -/
private theorem affine_retract_sections {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (m : ℕ) (ι : M ⟶ SheafOfModules.free (ULift.{u} (Fin m)))
    (π : SheafOfModules.free (ULift.{u} (Fin m)) ⟶ M) (h : ι ≫ π = 𝟙 M) :
    M.IsQuasicoherent ∧ Module.Finite R Γ(M, ⊤) ∧ Module.Projective R Γ(M, ⊤) := by
  let H : Retract M (SheafOfModules.free (ULift.{u} (Fin m))) := ⟨ι, π, h⟩
  let G := moduleSpecΓFunctor (R := R)
  let e : G.obj (SheafOfModules.free (ULift.{u} (Fin m))) ≅
      ModuleCat.of R (ULift.{u} (Fin m) →₀ R) :=
    (G.mapIso (tildeFinsupp (R := R) (ULift.{u} (Fin m)))).symm ≪≫
      (tilde.toTildeΓNatIso (R := R)).symm.app _
  have : Module.Finite R (G.obj (SheafOfModules.free (ULift.{u} (Fin m)))) :=
    Module.Finite.equiv e.toLinearEquiv.symm
  have : Module.Projective R (G.obj (SheafOfModules.free (ULift.{u} (Fin m)))) :=
    Module.Projective.of_equiv' e.toLinearEquiv.symm
  let H' := H.map G
  have hlin : H'.r.hom.comp H'.i.hom = LinearMap.id := by
    exact congrArg ModuleCat.Hom.hom H'.retract
  have hf : Module.Finite R (G.obj M) := Module.Finite.of_surjective H'.r.hom (by
    intro x
    exact ⟨H'.i.hom x, congrArg (fun f => f x) hlin⟩)
  have hp : Module.Projective R (G.obj M) :=
    Module.Projective.of_split H'.i.hom H'.r.hom hlin
  have hi : IsIso M.fromTildeΓ :=
    MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _)
      ((tilde.adjunction (R := R)).counit.retractArrowApp H)
      (show IsIso (Modules.fromTildeΓ (R := R)
        (SheafOfModules.free (ULift.{u} (Fin m)))) from inferInstance)
  exact ⟨(isQuasicoherent_iff_isIso_fromTildeΓ M).2 hi, hf, hp⟩

/-- A single retract of a finite free sheaf is finite free near a specified point.

Source: Stacks Project, Tag 00NX (3) implies (7), and Tags 01IA and 01IB.
Proof: Choose an affine neighbourhood W of x inside U. Transport the splitting
along open restriction, the over-site equivalence, and W's isomorphism to its
spectrum. These functors preserve finite free sheaves. Applying global sections
preserves the splitting; the sections of the ambient free sheaf are finite free,
by tildeFinsupp and the tilde-Gamma unit. Hence the sections of the retract are
finite projective. Naturality of the affine counit makes its component at the
retract a retract of its component at the free sheaf. The latter is invertible,
so the former is invertible too, proving quasi-coherence of the retract.
Apply the finite-projective prime-local-free lemma at the prime representing x.
It gives f outside that prime and a finite basis after localization away from f.
The source library's localized-sections comparison gives a free sheaf on Spec A_f.
Its open-immersion image in X is affine, contains x, and lies inside W and U.
Restrict along the inverse isomorphism onto that image, compose the restriction
comparisons, and use the over-site equivalence to recover the required isomorphism.
Rank zero is allowed; if U is empty no x satisfies hx.
(blueprint: new-pc-single-retract-sheaf-affine-trivialization). -/
theorem exists_affine_trivialization_of_finite_retract
    (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (hM : ∃ m : ℕ,
      ∃ (ι : M ⟶ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)) ⟶ M),
        ι ≫ π = 𝟙 M)
    (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ hVU : V ≤ U, IsAffine V.toScheme ∧
      ∃ r : ℕ, Nonempty
        ((SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVU)).obj M ≅
          SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin r))) := by
  classical
  obtain ⟨m, ι, π, hsplit⟩ := hM
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
  let F := SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hWU)
  let E := (Modules.overEquiv W).functor
  let K := Modules.restrictFunctor hW.isoSpec.inv
  let T := F ⋙ E ⋙ K
  let N : (Spec Γ(X, W)).Modules := T.obj M
  let eunit := (K.mapIso (E.mapIso (SheafOfModules.overMapUnitIso
    (R := moduleRings X.toRingedSpace) (homOfLE hWU)) ≪≫
    (Modules.overEquivFunctorObjUnitIso W).symm) ≪≫
    Modules.restrictUnitIso hW.isoSpec.inv).symm
  have : PreservesColimitsOfShape (Discrete (ULift.{u} (Fin m))) F := by
    dsimp [F]
    infer_instance
  have : PreservesColimitsOfShape (Discrete (ULift.{u} (Fin m))) T := by
    dsimp [T, E, K]
    infer_instance
  let efree := (SheafOfModules.mapFreeIso T (ULift.{u} (Fin m)) eunit).symm
  have hs : (T.map ι ≫ efree.hom) ≫ (efree.inv ≫ T.map π) = 𝟙 N := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← T.map_comp, hsplit, T.map_id]
    rfl
  obtain ⟨hqc, hfin, hproj⟩ :=
    affine_retract_sections N m (T.map ι ≫ efree.hom) (efree.inv ≫ T.map π) hs
  have : N.IsQuasicoherent := hqc
  have : Module.Finite Γ(X, W) Γ(N, ⊤) := hfin
  have : Module.Projective Γ(X, W) Γ(N, ⊤) := hproj
  obtain ⟨p, hp⟩ : ∃ p : Spec Γ(X, W), hW.fromSpec p = x := by
    have hx' : x ∈ hW.fromSpec.opensRange := by
      simpa only [hW.opensRange_fromSpec] using hxW
    exact hx'
  obtain ⟨f, hf, r, ⟨eb⟩⟩ :=
    Module.exists_localizationAway_equiv_finsupp_of_finite_projective
      (M := Γ(N, ⊤)) p.asIdeal
  let j := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, W) (Localization.Away f)))
  obtain ⟨ef⟩ := Modules.nonempty_restrict_iso_free_of_localizedModule N f
    (eb ≪≫ₗ Finsupp.domLCongr Equiv.ulift.symm)
  have hpj : p ∈ j.opensRange := by
    rw [Hom.opensRange_localizationAway]
    exact (PrimeSpectrum.mem_basicOpen f p).2 hf
  obtain ⟨q, hq⟩ : ∃ q, j q = p := hpj
  let t := j ≫ hW.isoSpec.inv
  let k := t ≫ W.ι
  let V := k.opensRange
  have hxV : x ∈ V := by
    refine ⟨q, ?_⟩
    change hW.fromSpec (j q) = x
    rw [hq, hp]
  have hVW : V ≤ W := by
    dsimp [V, k]
    rw [Hom.opensRange_comp]
    exact (W.ι.image_le_opensRange _).trans (by simp)
  have hVU : V ≤ U := hVW.trans hWU
  refine ⟨V, hxV, hVU, isAffineOpen_opensRange k, r, ⟨?_⟩⟩
  let L := E.obj (F.obj M)
  let et : L.restrict t ≅ SheafOfModules.free (ULift.{u} (Fin r)) :=
    Modules.restrictCompIso L hW.isoSpec.inv j t rfl ≪≫ ef
  let g := k.isoOpensRange.inv ≫ t
  let eg : L.restrict g ≅ SheafOfModules.free (ULift.{u} (Fin r)) :=
    Modules.restrictCompIso L t k.isoOpensRange.inv g rfl ≪≫
      (Modules.restrictFunctor k.isoOpensRange.inv).mapIso et ≪≫
      Modules.restrictFreeIso k.isoOpensRange.inv (ULift.{u} (Fin r))
  have hg : g = X.homOfLE hVW := by
    apply (cancel_mono W.ι).1
    rw [homOfLE_ι]
    change k.isoOpensRange.inv ≫ k = V.ι
    exact k.isoOpensRange_inv_comp
  let ev : L.restrict (X.homOfLE hVW) ≅ SheafOfModules.free (ULift.{u} (Fin r)) :=
    (Modules.restrictFunctorCongr hg).symm.app L ≪≫ eg
  let H := (Modules.overEquiv V).functor
  let ec := (Modules.overMapCompOverEquiv (homOfLE hVW)).app (F.obj M)
  exact H.preimageIso (ec ≪≫ ev ≪≫ SheafOfModules.mapFreeIso H (ULift.{u} (Fin r))
    (Modules.overEquivFunctorObjUnitIso V))

end AlgebraicGeometry.Scheme
