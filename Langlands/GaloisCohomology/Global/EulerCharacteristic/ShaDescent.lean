import Langlands.GaloisCohomology.CompactSupport.OpenSubgroup
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Descent
import Langlands.GaloisCohomology.Global.Localization
import Langlands.GaloisCohomology.Global.Units.DivisorSequence

/-!
# Tate–Shafarevich classes of a family and their descent to an open subgroup

For a family of continuous homomorphisms `φ_v : H_v → G`, `shaSubmodule φ A n` (of
`Langlands.GaloisCohomology.Global.Localization`) is the submodule of the classes of `Hⁿ(G, A)` that
vanish on every `H_v`; it is preserved by the maps of coefficients
(`coeffMap_mem_shaSubmodule`).

For an open normal subgroup `V` whose index is invertible on `A`, the family of `V` is the Mackey
family `mackeyFamily V φ` (the local groups `{h ∈ H_v | x φ_v(h) x⁻¹ ∈ V}` for the double cosets
`V x φ_v(H_v)`), and a class vanishes on every `H_v` exactly when its restriction to `V` vanishes on
the Mackey family (`mem_shaSubmodule_iff_res`): restriction along `h ↦ x φ_v(h) x⁻¹` has the kernel
of restriction along `φ_v` to the open subgroup `{h | x φ_v(h) x⁻¹ ∈ V}` (`map_conj_apply_eq_zero_iff`),
which is injective on `Hⁿ(H_v, A)` since its index divides that of `V`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology

universe u

noncomputable section

section Sha

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

/-- Restriction along `φ_v` commutes with a map of coefficients. -/
theorem map_coeffMap_apply {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] (f : A ⟶ B) (v : ι)
    {n : ℕ} (x : cohomology A n) :
    (map (φ v) (𝟙 (Rep.res (φ v : Hv v →* G) B)) n).hom ((coeffMap f n).hom x) =
      (coeffMap ((Rep.resFunctor (φ v : Hv v →* G)).map f) n).hom
        ((map (φ v) (𝟙 (Rep.res (φ v : Hv v →* G) A)) n).hom x) := by
  rw [map_coeffMap_hom_apply, ← ModuleCat.comp_apply, map_comp_coeffMap, Category.comp_id,
    Category.id_comp]

/-- A map of coefficients sends classes vanishing on the family to classes vanishing on the
family. -/
theorem coeffMap_mem_shaSubmodule {A B : Rep.{u} k G} [IsSmoothRep A] [IsSmoothRep B] (f : A ⟶ B)
    {n : ℕ} {x : cohomology A n} (hx : x ∈ shaSubmodule φ A n) :
    (coeffMap f n).hom x ∈ shaSubmodule φ B n := fun v => by
  rw [map_coeffMap_apply, hx v, map_zero]

end Sha

section Descent

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {ι : Type u} {Hv : ι → Type u} [∀ v, Group (Hv v)]
  [∀ v, TopologicalSpace (Hv v)] [∀ v, IsTopologicalGroup (Hv v)] [∀ v, CompactSpace (Hv v)]
  (φ : ∀ v, Hv v →ₜ* G) (V : OpenSubgroup G) (A : Rep.{u} k G) [IsSmoothRep A]

/-- The homomorphism `h ↦ φ_v(h)` from the local group at `p = (v, d)` of the Mackey family to `G`. -/
abbrev mackeyLocalHom (p : MackeyIndex V φ) : mackeyGroup V φ p →ₜ* G :=
  (φ p.1).comp (subgroupInclusion (mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out))

omit [CompactSpace G] [∀ v, CompactSpace (Hv v)] in
/-- The restriction of `A` to `V` and then to a local group of the Mackey family is smooth. -/
instance isSmoothRep_res_mackeyFamily (p : MackeyIndex V φ) :
    IsSmoothRep (Rep.res (mackeyFamily V φ p : mackeyGroup V φ p →* (V : Subgroup G))
      (Rep.res (V : Subgroup G).subtype A)) :=
  isSmoothRep_res (mackeyFamily V φ p) (Rep.res (V : Subgroup G).subtype A)

omit [CompactSpace G] [∀ v, CompactSpace (Hv v)] in
/-- Restriction to `V` followed by restriction along the Mackey family at `p = (v, d)` is
restriction along `h ↦ x φ_v(h) x⁻¹`, `x` the representative of `d`. -/
theorem map_mackeyFamily_res (p : MackeyIndex V φ) (n : ℕ) (y : cohomology A n) :
    (map (mackeyFamily V φ p) (𝟙 _) n).hom ((res A (V : Subgroup G) n).hom y) =
      (map ((subgroupInclusion (V : Subgroup G)).comp (mackeyFamily V φ p)) (𝟙 _) n).hom y := by
  have : IsSmoothRep (Rep.res (subgroupInclusion (V : Subgroup G) : (V : Subgroup G) →* G) A) :=
    isSmoothRep_res _ A
  have : IsSmoothRep (Rep.res (mackeyFamily V φ p : mackeyGroup V φ p →* (V : Subgroup G))
      (Rep.res (subgroupInclusion (V : Subgroup G) : (V : Subgroup G) →* G) A)) :=
    isSmoothRep_res _ _
  refine (map_map_apply (subgroupInclusion (V : Subgroup G)) (𝟙 _) (mackeyFamily V φ p) (𝟙 _) n
    y).trans ?_
  exact congrArg (fun F => F.hom y) (ProfiniteCohomology.map_congr (A := A)
    (B := Rep.res (((subgroupInclusion (V : Subgroup G)).comp (mackeyFamily V φ p) :
      mackeyGroup V φ p →ₜ* G) : mackeyGroup V φ p →* G) A) _ _ rfl (fun _ => rfl) n)

omit [∀ v, CompactSpace (Hv v)] in
/-- Restriction along the Mackey family at `p = (v, d)` of the restriction to `V` vanishes exactly
when the restriction to `H_v` and then to the local group at `p` vanishes. -/
theorem map_mackeyFamily_res_eq_zero_iff (p : MackeyIndex V φ) (n : ℕ) (y : cohomology A n) :
    (map (mackeyFamily V φ p) (𝟙 _) n).hom ((res A (V : Subgroup G) n).hom y) = 0 ↔
      (res (Rep.res (φ p.1 : Hv p.1 →* G) A)
        (mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out) n).hom
          ((map (φ p.1) (𝟙 (Rep.res (φ p.1 : Hv p.1 →* G) A)) n).hom y) = 0 := by
  have : IsSmoothRep (Rep.res (subgroupInclusion (mackeySubgroup (V : Subgroup G)
      (φ p.1).toMonoidHom p.2.out) : mackeyGroup V φ p →* Hv p.1) (Rep.res (φ p.1 : Hv p.1 →* G) A)) :=
    isSmoothRep_res _ _
  have h2 : (res (Rep.res (φ p.1 : Hv p.1 →* G) A)
      (mackeySubgroup (V : Subgroup G) (φ p.1).toMonoidHom p.2.out) n).hom
        ((map (φ p.1) (𝟙 (Rep.res (φ p.1 : Hv p.1 →* G) A)) n).hom y) =
      (map (mackeyLocalHom φ V p) (𝟙 _) n).hom y := by
    refine (map_map_apply (φ p.1) (𝟙 _) (subgroupInclusion (mackeySubgroup (V : Subgroup G)
      (φ p.1).toMonoidHom p.2.out)) (𝟙 _) n y).trans ?_
    exact congrArg (fun F => F.hom y) (ProfiniteCohomology.map_congr (A := A)
      (B := Rep.res ((mackeyLocalHom φ V p : mackeyGroup V φ p →ₜ* G) : mackeyGroup V φ p →* G) A)
      _ _ rfl (fun _ => rfl) n)
  rw [map_mackeyFamily_res, h2]
  refine map_conj_apply_eq_zero_iff A (mackeyLocalHom φ V p)
    ((subgroupInclusion (V : Subgroup G)).comp (mackeyFamily V φ p)) p.2.out⁻¹ (fun h => ?_) n y
  change p.2.out * (φ p.1) (h : Hv p.1) * p.2.out⁻¹ = p.2.out⁻¹⁻¹ * (φ p.1) (h : Hv p.1) * p.2.out⁻¹
  rw [inv_inv]

variable [(V : Subgroup G).Normal]

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- The index of a Mackey subgroup divides the index of the normal subgroup `V`. -/
theorem index_mackeySubgroup_dvd {H : Type u} [Group H] (ψ : H →* G) (x : G) :
    (mackeySubgroup (V : Subgroup G) ψ x).index ∣ (V : Subgroup G).index := by
  rw [mackeySubgroup, Subgroup.index_comap]
  exact Subgroup.relIndex_dvd_index_of_normal _ _

/-- **Descent to an open normal subgroup.** If multiplication by `[G : V]` is bijective on `A`, a
class of `Hⁿ(G, A)` vanishes on every `H_v` exactly when its restriction to `V` vanishes on the
Mackey family of `V`. -/
theorem mem_shaSubmodule_iff_res (hA : Function.Bijective fun a : A => (V : Subgroup G).index • a)
    (n : ℕ) (y : cohomology A n) :
    y ∈ shaSubmodule φ A n ↔
      (res A (V : Subgroup G) n).hom y ∈
        shaSubmodule (mackeyFamily V φ) (Rep.res (V : Subgroup G).subtype A) n := by
  constructor
  · intro hy p
    rw [map_mackeyFamily_res_eq_zero_iff, hy p.1, map_zero]
  · intro hy v
    let p : MackeyIndex V φ := ⟨v, DoubleCoset.mk (V : Subgroup G) (φ v).toMonoidHom.range 1⟩
    have h0 := (map_mackeyFamily_res_eq_zero_iff φ V A p n y).1 (hy p)
    have hB : Function.Bijective fun a : Rep.res (φ p.1 : Hv p.1 →* G) A =>
        ((mackeyOpenSubgroup V (φ p.1).continuous p.2.out : OpenSubgroup (Hv p.1)) :
          Subgroup (Hv p.1)).index • a :=
      bijective_nsmul_of_dvd (index_mackeySubgroup_dvd V (φ p.1).toMonoidHom p.2.out) hA
    exact cohomologyRes_injective_of_bijective (mackeyOpenSubgroup V (φ p.1).continuous p.2.out)
      (Rep.res (φ p.1 : Hv p.1 →* G) A) hB n (h0.trans (map_zero _).symm)

end Descent

end

end Langlands.GaloisCohomology
