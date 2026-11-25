import Langlands.Theta.Metaplectic.Defs
import Langlands.Theta.Heisenberg.StoneVonNeumann

/-!
# The metaplectic group is an extension of the symplectic group by `ℂˣ`

GKT §2.1.1–§2.1.2 (pp. 47–49). Let `F` be a nonarchimedean local field with `2` invertible, `W` a
finite-dimensional `F`-vector space with its module topology, `B` a non-degenerate alternating form
on `W`, `ψ` a non-trivial continuous character of `F`, and `ρ` a smooth irreducible representation
of `HeisenbergGroup B` with central character `ψ` (a model of the Heisenberg representation). Then

`1 → ℂˣ → MetaplecticGroup ρ → Sp(W) → 1`

is exact: the kernel of the projection is the group of scalars (`MetaplecticGroup.ker_proj`, by
Schur's lemma), and the projection is surjective (`MetaplecticGroup.proj_surjective`: for each
isometry `g`, the representation `h ↦ ρ(g · h)` is again smooth, irreducible, with central
character `ψ`, hence isomorphic to `ρ` by the Stone–von Neumann theorem, and an isomorphism `M`
gives `(g, M)`).

Consequences: the change of model `MetaplecticGroup.congr e` does not depend on the isomorphism
`e` (`congr_eq`, GKT Proposition 6.8 (1)); two elements with the same projection differ by a
scalar (`exists_scalar_mul_eq`); two splittings of the same `ι : G →* Sp(W)` differ by a character
of `G` (`Splitting.exists_eq_twist`, GKT §12.2.1).
-/

noncomputable section

open Topology

namespace Langlands

/-- Irreducibility is unchanged by composing with an automorphism of the group. -/
theorem isIrreducible_comp_mulEquiv_iff {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (φ : G ≃* G) :
    Representation.IsIrreducible (ρ.comp φ.toMonoidHom) ↔ ρ.IsIrreducible := by
  let e : Subrepresentation (ρ.comp φ.toMonoidHom) ≃o Subrepresentation ρ :=
    { toFun := fun P => ⟨P.toSubmodule, fun g v hv => by
        have := P.apply_mem_toSubmodule (φ.symm g) hv
        simpa using this⟩
      invFun := fun P => ⟨P.toSubmodule, fun g v hv => P.apply_mem_toSubmodule (φ g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact e.isSimpleOrder_iff

/-- An irreducible representation is on a non-zero space. -/
theorem nontrivial_of_isIrreducible {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) : Nontrivial V := by
  have : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hi
  exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule

end Langlands

namespace Langlands.HeisenbergGroup

open Langlands.LinearMap.BilinForm (isometryGroup)

universe u v w

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)] {W : Type v} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
  [TopologicalSpace W] [IsModuleTopology F W] {B : LinearMap.BilinForm F W}
  {S : Type w} [AddCommGroup S] [Module ℂ S] {ρ : Representation ℂ (HeisenbergGroup B) S}


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W]
  [TopologicalSpace W] [IsModuleTopology F W] in
/-- The representation `h ↦ ρ(g · h)` has the central character of `ρ`. -/
theorem hasCentralCharacter_comp_isometryAction {ψ : AddChar F ℂ} (hc : HasCentralCharacter ρ ψ)
    (g : isometryGroup B) : HasCentralCharacter (ρ.comp (isometryAction B g).toMonoidHom) ψ :=
  fun t v => by
    change ρ (isometryAction B g (central t)) v = _
    rw [isometryAction_central, hc]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W] in
/-- An isometry acts continuously on the Heisenberg group. -/
theorem continuous_isometryAction (g : isometryGroup B) : Continuous (isometryAction B g) := by
  have := IsModuleTopology.toContinuousAdd F W
  have hg : Continuous ((g : W ≃ₗ[F] W) : W → W) :=
    IsModuleTopology.continuous_of_linearMap (g : W ≃ₗ[F] W).toLinearMap
  exact continuous_mk (hg.comp continuous_vec) continuous_cen

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W] in
/-- The representation `h ↦ ρ(g · h)` of a smooth `ρ` is smooth. -/
theorem isSmooth_comp_isometryAction (hρ : IsSmooth ρ) (g : isometryGroup B) :
    IsSmooth (ρ.comp (isometryAction B g).toMonoidHom) := by
  intro v
  obtain ⟨K, hK⟩ := hρ v
  refine ⟨K.comap (isometryAction B g).toMonoidHom (continuous_isometryAction g),
    (Representation.mem_invariants _ v).2 fun k => ?_⟩
  exact (Representation.mem_invariants _ v).1 hK ⟨isometryAction B g k, k.2⟩

end Langlands.HeisenbergGroup

namespace Langlands.Theta

open HeisenbergGroup
open Langlands.LinearMap.BilinForm (isometryGroup)

universe u v w w'

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Invertible (2 : F)] {W : Type v} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
  [TopologicalSpace W] [IsModuleTopology F W] {B : LinearMap.BilinForm F W}
  {S : Type w} [AddCommGroup S] [Module ℂ S] {ρ : Representation ℂ (HeisenbergGroup B) S}


namespace MetaplecticGroup

/-- **Schur's lemma**: for a smooth irreducible `ρ`, the kernel of the projection is the group of
scalars `(1, z)` (GKT p. 49). -/
theorem ker_proj (hρ : IsSmooth ρ) (hi : ρ.IsIrreducible) : (proj ρ).ker = (scalar ρ).range := by
  have : Nontrivial S := nontrivial_of_isIrreducible hi
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker, proj_apply] at hx
    let e' : Representation.Equiv ρ ρ := Representation.Equiv.mk x.1.2 fun h => by
      have := x.2 h
      rwa [hx, map_one, MulAut.one_apply] at this
    obtain ⟨c, hc⟩ := equiv_eq_smul hρ hi (Representation.Equiv.refl ρ) e'
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨v, hv⟩ := exists_ne (0 : S)
      have h1 : x.1.2 v = 0 := by simpa using hc v
      exact hv (x.1.2.injective (h1.trans (map_zero _).symm))
    refine ⟨Units.mk0 c hc0, ?_⟩
    ext w
    · rw [hx]; rfl
    · exact (hc w).symm
  · rintro _ ⟨z, rfl⟩
    rw [MonoidHom.mem_ker, proj_scalar]

/-- Two elements of the metaplectic group with the same projection differ by a scalar. -/
theorem exists_scalar_mul_eq (hρ : IsSmooth ρ) (hi : ρ.IsIrreducible) {x y : MetaplecticGroup ρ}
    (h : proj ρ x = proj ρ y) : ∃ z : ℂˣ, y = scalar ρ z * x := by
  have : y * x⁻¹ ∈ (proj ρ).ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  rw [ker_proj hρ hi] at this
  obtain ⟨z, hz⟩ := this
  exact ⟨z, by rw [hz, inv_mul_cancel_right]⟩

/-- **Stone–von Neumann**: the projection of the metaplectic group of a model of the Heisenberg
representation onto the symplectic group is surjective (GKT §2.1.1, p. 47). -/
theorem proj_surjective {ψ : AddChar F ℂ} (hB : B.IsAlt) (hn : B.Nondegenerate)
    (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (hρ : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (hc : HasCentralCharacter ρ ψ) : Function.Surjective (proj ρ) := by
  intro g
  obtain ⟨e⟩ := nonempty_equiv hB hn hψ hψ1 hρ hi hc
    (isSmooth_comp_isometryAction hρ g)
    ((isIrreducible_comp_mulEquiv_iff ρ (isometryAction B g)).2 hi)
    (hasCentralCharacter_comp_isometryAction hc g)
  refine ⟨⟨(g, e.toLinearEquiv), fun h => LinearMap.ext fun v => ?_⟩, rfl⟩
  exact Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap h v

/-- **The exact sequence** `1 → ℂˣ → MetaplecticGroup ρ → Sp(W) → 1` (GKT p. 49): `scalar` is
injective, its range is the kernel of `proj`, and `proj` is surjective. -/
theorem exact {ψ : AddChar F ℂ} (hB : B.IsAlt) (hn : B.Nondegenerate) (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (hρ : IsSmooth ρ) (hi : ρ.IsIrreducible) (hc : HasCentralCharacter ρ ψ) :
    Function.Injective (scalar ρ) ∧ (proj ρ).ker = (scalar ρ).range ∧
      Function.Surjective (proj ρ) :=
  have : Nontrivial S := nontrivial_of_isIrreducible hi
  ⟨scalar_injective ρ, ker_proj hρ hi, proj_surjective hB hn hψ hψ1 hρ hi hc⟩

/-- **The change of model does not depend on the isomorphism** (GKT Proposition 6.8 (1)): two
isomorphisms of a smooth irreducible model differ by a scalar, which conjugation does not see. -/
theorem congr_eq {S' : Type w'} [AddCommGroup S'] [Module ℂ S']
    {ρ' : Representation ℂ (HeisenbergGroup B) S'} (hρ : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (e e' : Representation.Equiv ρ ρ') : congr e = congr e' := by
  have : Nontrivial S := nontrivial_of_isIrreducible hi
  obtain ⟨c, hc⟩ := equiv_eq_smul hρ hi e e'
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := exists_ne (0 : S)
    have h1 : e' v = 0 := by simpa using hc v
    exact hv (e'.toLinearEquiv.injective (h1.trans (map_zero _).symm))
  have hsymm : ∀ w, e'.symm w = c⁻¹ • e.symm w := fun w => by
    apply e'.toLinearEquiv.injective
    change e' (e'.symm w) = e' (c⁻¹ • e.symm w)
    rw [Representation.Equiv.apply_symm_apply, map_smul, hc, smul_smul, inv_mul_cancel₀ hc0,
      one_smul, Representation.Equiv.apply_symm_apply]
  ext x w
  · rfl
  · change e (x.1.2 (e.symm w)) = e' (x.1.2 (e'.symm w))
    rw [hsymm, map_smul, hc, map_smul, smul_smul, mul_inv_cancel₀ hc0, one_smul]

namespace Splitting

variable {G : Type*} [Group G] {ι : G →* isometryGroup B}

/-- **Two splittings differ by a character** (GKT §12.2.1): for a smooth irreducible model, if
`s` and `s'` both lift `ι`, then `s' = α · s` for a character `α : G →* ℂˣ`. -/
theorem exists_eq_twist (hρ : IsSmooth ρ) (hi : ρ.IsIrreducible) (s s' : Splitting ρ ι) :
    ∃ α : G →* ℂˣ, s' = s.twist α := by
  have : Nontrivial S := nontrivial_of_isIrreducible hi
  have hmem : ∀ g, ∃ z : ℂˣ, scalar ρ z = s'.toMonoidHom g * (s.toMonoidHom g)⁻¹ := fun g => by
    have : s'.toMonoidHom g * (s.toMonoidHom g)⁻¹ ∈ (proj ρ).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, s.proj_apply, s'.proj_apply, mul_inv_cancel]
    rw [ker_proj hρ hi] at this
    exact this
  choose a ha using hmem
  have hinj := scalar_injective ρ
  let α : G →* ℂˣ :=
    { toFun := a
      map_one' := hinj (by rw [ha, map_one, map_one, inv_one, mul_one, map_one])
      map_mul' := fun g h => hinj (by
        rw [map_mul, ha, ha, ha, map_mul, map_mul, mul_inv_rev]
        calc s'.toMonoidHom g * s'.toMonoidHom h * ((s.toMonoidHom h)⁻¹ * (s.toMonoidHom g)⁻¹)
            = s'.toMonoidHom g * (s'.toMonoidHom h * (s.toMonoidHom h)⁻¹) *
                (s.toMonoidHom g)⁻¹ := by group
          _ = s'.toMonoidHom g * scalar ρ (a h) * (s.toMonoidHom g)⁻¹ := by rw [ha]
          _ = s'.toMonoidHom g * (s.toMonoidHom g)⁻¹ * scalar ρ (a h) := by
            rw [mul_assoc, scalar_mul_comm, ← mul_assoc]
          _ = _ := by rw [ha]) }
  refine ⟨α, Splitting.ext (MonoidHom.ext fun g => ?_)⟩
  change s'.toMonoidHom g = scalar ρ (a g) * s.toMonoidHom g
  rw [ha, inv_mul_cancel_right]

end Splitting

end MetaplecticGroup

end Langlands.Theta
