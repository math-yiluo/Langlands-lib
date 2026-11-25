/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PicTorsionPairing
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorExtensionTransport

/-!
# The pairing between torsors and torsion line bundles is invariant under automorphisms

Let `X` be a smooth proper curve over an algebraically closed field `k` and `f : X ⟶ X` an
automorphism of schemes lying over an automorphism `σ` of `Spec k`, which need not be the
identity: for instance the geometric Galois Frobenius of the geometric fibre of a curve over a
finite field. Restriction along `f` acts on étale cohomology
(`AlgebraicGeometry.Scheme.etaleRestrictionH`); it is the pullback of line bundles on
`H¹(X, 𝔾ₘ) = Pic(X)`, it commutes with the Kummer maps, and it preserves the trace
`H²(X, μ_m) ≅ ℤ/m` since the degree of line bundles is invariant under pullback along `f`
(`AlgebraicGeometry.Scheme.picDegreeHom_map_of_comp_eq`). Together with the invariance of the
cup product (`AlgebraicGeometry.Scheme.EtaleTorsor.restrictMu_cupMu`) this shows that the
character of `Pic(X)[m]` attached to the transport of a torsor along `f` is the character of
the torsor precomposed with `f^*` (`AlgebraicGeometry.Scheme.EtaleTorsor.picPairing_transport`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  (f : X ⟶ X) [IsIso f] (σ : Spec (.of k) ⟶ Spec (.of k)) [IsIso σ]
  (hf : f ≫ (X ↘ Spec (.of k)) = (X ↘ Spec (.of k)) ≫ σ)

include hf in
/-- **The degree is invariant under automorphisms.** The degree of line bundles on a smooth
proper curve over `k` is invariant under pullback along an automorphism `f` of the curve lying
over an automorphism `σ` of `Spec k`, which need not be `k`-linear. -/
lemma picDegreeHom_map_of_comp_eq [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (L : X.Pic) :
    picDegreeHom k X (Pic.map f L) = picDegreeHom k X L := by
  have sq : IsPullback f (X ↘ Spec (.of k)) (X ↘ Spec (.of k)) σ :=
    IsPullback.of_horiz_isIso ⟨hf⟩
  have hL : Pic.map f L = Pic.ofIsInvertible ((Modules.pullback f).obj
      ((fromSkeleton X.Modules).obj L.val)) :=
    Pic.ext rfl
  rw [hL, picDegreeHom_ofIsInvertible, Modules.degree_pullback_of_isPullback σ f sq,
    ← picDegreeHom_ofIsInvertible, Pic.ofIsInvertible_fromSkeleton]

variable [IsAlgClosed k]

/-- An automorphism is étale. -/
local instance : Etale f := MorphismProperty.of_isIso @Etale f

/-- The restriction map `H^q(X, μ_m) ⟶ H^q(X, R μ_m) ≅ H^q(X, μ_m)` along `f`. -/
noncomputable abbrev restrictMuH (m q : ℕ) :
    Sheaf.H (X.rootsOfUnitySheaf m) q →+ Sheaf.H (X.rootsOfUnitySheaf m) q :=
  (Sheaf.H.map (rootsOfUnityRestrictionIso f m).hom q).comp (etaleRestrictionH f _ q)

/-- Restriction along `f` is compatible with the Kummer identification `H¹(X, μ_m) ≅ Pic(X)[m]`
and the pullback of line bundles along `f`. -/
lemma coe_kummerTorsionEquiv_restrictMuH [IsProper (X ↘ Spec (.of k))] (m : ℕ)
    (hm : (m : k) ≠ 0) (x : Sheaf.H (X.rootsOfUnitySheaf m) 1) :
    (kummerTorsionEquiv m hm (restrictMuH f m 1 x) : Additive X.Pic) =
      (Pic.mapHom f).toAdditive (kummerTorsionEquiv m hm x : Additive X.Pic) := by
  have e : Sheaf.H.map (kernel.ι (m • 𝟙 X.gmSheaf)) 1
      (Sheaf.H.map (rootsOfUnityRestrictionIso f m).hom 1 (etaleRestrictionH f _ 1 x)) =
      etaleRestrictionH f X.gmSheaf 1 (Sheaf.H.map (kernel.ι (m • 𝟙 X.gmSheaf)) 1 x) := by
    refine (Sheaf.H.map_comp_apply _ _ _).symm.trans ?_
    rw [rootsOfUnityRestrictionIso_hom_ι, etaleRestrictionH_map]
    rfl
  rw [coe_kummerTorsionEquiv_apply, coe_kummerTorsionEquiv_apply, AddMonoidHom.comp_apply, e]
  obtain ⟨L, hL⟩ := (Pic.toCohomologicalPicardGroupAddEquiv X).surjective
    (Sheaf.H.map (kernel.ι (m • 𝟙 X.gmSheaf)) 1 x)
  rw [← hL, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_eq]
  exact etaleRestrictionH_toCohomologicalPicardGroup f L.toMul

omit [IsAlgClosed k] in
/-- Restriction along `f` is compatible with the Kummer map `Pic(X) ⟶ H²(X, μ_m)` and the
pullback of line bundles along `f`. -/
lemma restrictMuH_picToSheafHTwo (m : ℕ) (hm : (m : k) ≠ 0) (L : Additive X.Pic) :
    restrictMuH f m 2 (picToSheafHTwo m hm L) =
      picToSheafHTwo m hm ((Pic.mapHom f).toAdditive L) := by
  have hS := X.kummerSequence_shortExact m (isUnit_natCast_appTop m hm)
  rw [AddMonoidHom.comp_apply]
  refine (congrArg (Sheaf.H.map (rootsOfUnityRestrictionIso f m).hom 2)
    (etaleRestrictionH_δSucc f hS 1 _)).trans ?_
  refine (Sheaf.H.map_δSucc _ hS (kummerSequenceRestriction f m) 1 _).trans ?_
  change Sheaf.H.δSucc hS 1 (Sheaf.H.map (𝟙 _) 1 _) = _
  rw [Sheaf.H.map_id_apply]
  exact congrArg (Sheaf.H.δSucc hS 1) (etaleRestrictionH_toCohomologicalPicardGroup f L.toMul)

include hf in
/-- **The trace is invariant under automorphisms.** Restriction along an automorphism `f` lying
over an automorphism of `Spec k` preserves the trace `H²(X, μ_m) ⟶ ℤ/m`: it is the degree modulo
`m` of line bundles, and the degree is invariant under pullback along `f`. -/
lemma sheafHTwoTrace_restrictMuH [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (m : ℕ) (hm : (m : k) ≠ 0)
    (z : Sheaf.H (X.rootsOfUnitySheaf m) 2) :
    sheafHTwoTrace m hm (restrictMuH f m 2 z) = sheafHTwoTrace m hm z := by
  obtain ⟨L, rfl⟩ := surjective_picToSheafHTwo m hm z
  rw [restrictMuH_picToSheafHTwo, sheafHTwoTrace_picToSheafHTwo, sheafHTwoTrace_picToSheafHTwo]
  change (((picDegreeHom k X (Pic.map f L.toMul)).toAdd : ℤ) : ZMod m) =
    (((picDegreeHom k X L.toMul).toAdd : ℤ) : ZMod m)
  rw [picDegreeHom_map_of_comp_eq f σ hf]

namespace EtaleTorsor

include hf in
/-- **Invariance of the pairing under automorphisms.** Let `f` be an automorphism of `X` lying
over an automorphism of `Spec k`, and let `t`, `t'` be `ℤ/m`-torsors with a morphism of total
spaces `h : P ⟶ P'` over `f` compatible with the actions, e.g. `t'` the transport of `t` along
`f`. Then the character of `t'` is that of `t` precomposed with the pullback `f^*` of line
bundles. -/
theorem picPairing_transport [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] {m : ℕ} [NeZero m] (hm : (m : k) ≠ 0)
    (t t' : EtaleTorsor (ULift.{u + 1} (ZMod m)) X) (h : t.P ⟶ t'.P) (hπ : t.π ≫ f = h ≫ t'.π)
    (hv : t.vadd 1 ≫ h = h ≫ t'.vadd 1)
    (y : AddSubgroup.torsionBy (Additive X.Pic) (m : ℤ)) :
    t'.picPairing hm y = t.picPairing hm ⟨(Pic.mapHom f).toAdditive y,
      AddSubgroup.apply_mem_torsionBy _ y.2⟩ := by
  rw [picPairing_apply, picPairing_apply, ← sheafHTwoTrace_restrictMuH f σ hf m hm,
    AddMonoidHom.comp_apply, t.restrictMu_cupMu f t' h hπ hv]
  congr 2
  apply (kummerTorsionEquiv m hm).injective
  apply Subtype.ext
  rw [AddEquiv.apply_symm_apply]
  exact (coe_kummerTorsionEquiv_restrictMuH f m hm _).trans
    (congrArg _ (congrArg Subtype.val ((kummerTorsionEquiv m hm).apply_symm_apply y)))

end EtaleTorsor

end AlgebraicGeometry.Scheme
