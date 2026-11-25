import Langlands.Sheaf.Equivariant.TwistedFiniteLocalSections

/-! # Discreteness after restriction to an object covered by a finite family -/

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory Opposite

universe w v u uG

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} {X : C}
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {ρ : G →* Aut X}

/-- The discrete sieve of a section contains a finite family whose sieve
becomes covering along the given restriction arrow. -/
def HasFiniteDiscreteCoverAfterRestriction {R : Type w} [CommRing R]
    (J : GrothendieckTopology (TwistedOver P ρ)) (L : LocalActionSystem (TwistedOver P ρ) G)
    (F : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R)
    {U U' : TwistedOver P ρ} (r : U' ⟶ U) (s : F.obj (op U)) : Prop :=
  ∃ (n : ℕ) (V : Fin n → TwistedOver P ρ) (f : ∀ i, V i ⟶ U),
    (∀ i, L.discreteSieve F s (f i)) ∧ (Sieve.ofArrows V f).pullback r ∈ J U'

/-- If a finite family in the discrete sieve of a section covers after
pullback to an admissible object, the restriction is discrete for the supplied
admissible action. The arrows in the pullback sieve can have arbitrary sources. -/
theorem isDiscreteSection_restriction_of_finite_discreteSieve_cover {R : Type w} [CommRing R]
    {J : GrothendieckTopology (TwistedOver P ρ)} {L : LocalActionSystem (TwistedOver P ρ) G}
    [L.HasAdmissibleRefinements J] (hL : L.IsLiftSystem)
    {F : (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat.{w} R} (hF : Presheaf.IsSheaf J F)
    {U U' : TwistedOver P ρ} {H H' : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ} {a' : (H' : Subgroup G) →* (End U')ᵐᵒᵖ}
    (ha : L.IsAdmissible U H a) (ha' : L.IsAdmissible U' H' a')
    (r : U' ⟶ U) (s : F.obj (op U))
    (hcov : HasFiniteDiscreteCoverAfterRestriction J L F r s) :
    IsDiscreteSection F a' (F.map r.op s) := by
  obtain ⟨n, V, f, hf, hcov⟩ := hcov
  choose W k p H₁ b hb hdisc hfac using hf
  have hloc (i : Fin n) : IsLocallyEquivariant a (b i) (p i) :=
    isLocallyEquivariant_of_isRestrictionEquivariant (hL _ _ _ ha) (hL _ _ _ (hb i))
      (LocalActionSystem.HasAdmissibleRefinements.isRestrictionEquivariant
        (J := J) ha (hb i) (p i))
  choose K hK hfix using hdisc
  choose M _ hM using fun i => hloc i (K i) (hK i)
  let N := H ⊓ OpenSubgroup.iInfOfFinite M
  have hN (g : (H : Subgroup G)) (hg : (g : G) ∈ N) (i : Fin n) :
      F.map (f i).op (F.map (a g).unop.asHom.op s) = F.map (f i).op s := by
    obtain ⟨j, hj, he⟩ :=
      hM i g (OpenSubgroup.iInfOfFinite_le M i (OpenSubgroup.mem_inf.mp hg).2)
    have hp : F.map (p i).op (F.map (a g).unop.asHom.op s) = F.map (p i).op s := by
      rw [← map_op_comp_apply, ← he, map_op_comp_apply, hfix i j hj]
    rw [← hfac i, map_op_comp_apply, map_op_comp_apply, hp]
  obtain ⟨N', hN', he⟩ :=
    LocalActionSystem.HasAdmissibleRefinements.isRestrictionEquivariant
      (J := J) ha ha' r N inf_le_left
  refine ⟨N', hN', fun h hh => ?_⟩
  obtain ⟨g, hg, hrg⟩ := he h hh
  rw [← map_op_comp_apply, hrg, map_op_comp_apply]
  refine isSeparated_of_isSheaf hF hcov ?_
  rintro Z q ⟨Y, l, _, ⟨i⟩, hq⟩
  calc
    _ = F.map (q ≫ r).op (F.map (a g).unop.asHom.op s) :=
      (map_op_comp_apply F q r _).symm
    _ = F.map l.op (F.map (f i).op (F.map (a g).unop.asHom.op s)) := by
      rw [← hq, map_op_comp_apply]
    _ = F.map l.op (F.map (f i).op s) := congrArg (fun t => F.map l.op t) (hN g hg i)
    _ = F.map q.op (F.map r.op s) := by
      rw [← map_op_comp_apply, hq, map_op_comp_apply]

end Langlands.Sheaf.Equivariant.TwistedOver
