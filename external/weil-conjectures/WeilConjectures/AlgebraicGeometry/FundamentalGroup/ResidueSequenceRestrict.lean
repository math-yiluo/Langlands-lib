/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ResidueSequence

/-!
# Residues under shrinking the open

Let `U ⊆ C` be a nonempty open of a smooth connected curve over an algebraically closed field
`k` and `U' ⊆ U` a smaller nonempty open. For the residue sequence of blueprint
`proposition-no-fixed-class-degree-one--1` we compare the residues of torsors on `U` and `U'`:

* the residues of a torsor on `U` are those of its restriction to `U'`
  (`AlgebraicGeometry.Scheme.EtaleTorsor.residue_pullback`);
* a torsor on `U` has vanishing residue at every closed point of `U`
  (`AlgebraicGeometry.Scheme.EtaleTorsor.residue_eq_zero_of_mem_range`);
* a torsor on `U'` whose residues vanish at the points of `U ∖ U'` extends to `U`
  (`AlgebraicGeometry.Scheme.EtaleTorsor.exists_isIsomorphic_pullback_of_residue_eq_zero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.EtaleTorsor

open FiniteEtale

section Pullback

variable {C U U' : Scheme.{u}} [IsIntegral C] (j : U ⟶ C) [IsOpenImmersion j] [Nonempty U]
  (ι : U' ⟶ U) [IsOpenImmersion ι] [Nonempty U']

local notation "Ω" => SeparableClosure (Scheme.functionField C)

@[reassoc]
lemma genericPointLift_comp_comp : genericPointLift (ι ≫ j) ≫ ι = genericPointLift j := by
  rw [← cancel_mono j, Category.assoc, genericPointLift_comp, genericPointLift_comp]

lemma genericGeometricPoint_comp_comp :
    (Etale.genericGeometricPoint (C := C) (ι ≫ j) : Spec (.of Ω) ⟶ _) ≫ ι =
      (Etale.genericGeometricPoint j : Spec (.of Ω) ⟶ _) := by
  simp only [Etale.genericGeometricPoint, pointOfAlgebra, Category.assoc,
    genericPointLift_comp_comp]

variable [ConnectedSpace U'] {N : ℕ} [NeZero N]

/-- The Galois character of the restriction of a torsor to a smaller open is the Galois
character of the torsor. -/
lemma galoisCharacter_pullback (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U) :
    (T.pullback ι).galoisCharacter (ι ≫ j) = T.galoisCharacter j := by
  funext σ
  set t' := (T.pullback ι).genericFiberPoint (ι ≫ j)
  have ht' : t' ≫ pullback.snd T.π ι = (Etale.genericGeometricPoint (ι ≫ j) : Spec (.of Ω) ⟶ _) :=
    (T.pullback ι).genericFiberPoint_comp (ι ≫ j)
  have ht : (t' ≫ pullback.fst T.π ι) ≫ T.π =
      (Etale.genericGeometricPoint j : Spec (.of Ω) ⟶ _) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht', genericGeometricPoint_comp_comp]
  refine (T.galoisCharacter_eq_of_specMap_comp_eq j σ _ ht ?_).symm
  have h := (T.pullback ι).specMap_comp_eq_comp_vadd_galoisCharacter (ι ≫ j) σ t'
    ((T.pullback ι).genericFiberPoint_comp (ι ≫ j))
  rw [← Category.assoc, h, Category.assoc, pullback_vadd, pullback.lift_fst, Category.assoc]

variable [IsLocallyNoetherian C] {k : Type u} [Field k] (p : C ⟶ Spec (.of k)) [NeZero (N : k)]
  [HasEnoughRootsOfUnity k N]

/-- Blueprint `proposition-no-fixed-class-degree-one--1`: the residues of a torsor on `U` are those
of its restriction to a smaller nonempty open `U'`. -/
lemma residue_pullback (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U) (z : C) :
    (T.pullback ι).residue (ι ≫ j) p z = T.residue j p z := by
  refine AddMonoidHom.ext fun ξ ↦ ?_
  rw [residue_apply, residue_apply, galoisCharacter_pullback]

end Pullback

/-- A closed point of a scheme smooth of relative dimension one over a field is not its generic
point: its local ring has dimension one. -/
lemma _root_.AlgebraicGeometry.Scheme.ne_genericPoint_of_isClosed {k : Type u} [Field k]
    {C : Scheme.{u}} [IsIntegral C] (p : C ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 p]
    {y : C} (hy : IsClosed ({y} : Set C)) : y ≠ genericPoint C := by
  rintro rfl
  have h := ringKrullDim_stalk_eq_one_of_smoothOfRelativeDimension_one p hy
  have : IsField (C.presheaf.stalk (genericPoint C)) := by
    change IsField C.functionField
    exact Field.toIsField _
  rw [ringKrullDim_eq_zero_of_isField this] at h
  exact zero_ne_one h

section Curve

open WeilGroup

variable {k : Type u} [Field k] [IsAlgClosed k] {C U : Scheme.{u}} {p : C ⟶ Spec (.of k)}
  [IsCurve p] [SmoothOfRelativeDimension 1 p] [ConnectedSpace C] [ConnectedSpace U]
  {j : U ⟶ C} [IsOpenImmersion j] [Nonempty U] [IsIntegral C] [IsLocallyNoetherian C]

local notation "Ω" => SeparableClosure (Scheme.functionField C)

omit [ConnectedSpace U] in
/-- Blueprint `proposition-no-fixed-class-degree-one--1`: a torsor on `U` has vanishing residue at
every closed point `y` of `U`, since it extends over `y`: compare with the restriction of the torsor
to `U ∖ {y}`. -/
theorem residue_eq_zero_of_mem_range {N : ℕ} [NeZero N] [NeZero (N : k)]
    (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U) {y : C} (hy : y ∈ Set.range j.base)
    (hyc : IsClosed ({y} : Set C)) : T.residue j p y = 0 := by
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  obtain ⟨u₀, rfl⟩ := hy
  have hinj := j.isOpenEmbedding.injective
  have hu₀ : IsClosed ({u₀} : Set U) := by
    have : ({u₀} : Set U) = j.base ⁻¹' {j.base u₀} := by
      ext x
      simp [hinj.eq_iff]
    rw [this]
    exact hyc.preimage j.base.hom.continuous
  let W : U.Opens := ⟨{u₀}ᶜ, hu₀.isOpen_compl⟩
  -- `W` contains the generic point
  have hgen : genericPoint C ∈ Set.range j.base := by
    obtain ⟨u⟩ := (inferInstance : Nonempty U)
    have := irreducibleSpace_of_smooth (p := p)
    exact ((genericPoint_spec C).specializes (Set.mem_univ (j u))).mem_open
      j.isOpenEmbedding.isOpen_range ⟨u, rfl⟩
  obtain ⟨u₁, hu₁⟩ := hgen
  have hu₁W : u₁ ∈ W := fun h ↦ ne_genericPoint_of_isClosed (p := p) hyc (by
    rw [← hu₁, show u₁ = u₀ from h])
  have : Nonempty W := ⟨⟨u₁, hu₁W⟩⟩
  have := irreducibleSpace_of_smooth (p := p)
  have : IrreducibleSpace W := (W.ι ≫ j).isOpenEmbedding.irreducibleSpace
  let V : C.Opens := j.opensRange
  have hV : Set.range (W.ι ≫ j).base ⊆ V := by
    rintro _ ⟨w, rfl⟩
    exact ⟨W.ι w, rfl⟩
  have hz : (V : Set C) \ Set.range (W.ι ≫ j).base = {j u₀} := by
    ext x
    constructor
    · rintro ⟨⟨u, rfl⟩, hx⟩
      by_contra hne
      have huW : u ∈ W := fun h ↦ hne (by rw [show u = u₀ from h]; rfl)
      exact hx ⟨⟨u, huW⟩, rfl⟩
    · rintro rfl
      refine ⟨⟨u₀, rfl⟩, ?_⟩
      rintro ⟨w, hw⟩
      have : W.ι w = u₀ := hinj hw
      exact w.2 this
  let s := (Etale.genericGeometricPoint (C := C) (W.ι ≫ j) : Spec (.of Ω) ⟶ _)
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup s
  rw [← residue_pullback j W.ι p T]
  refine (residue_eq_zero_iff_forall_monodromy_eq_one (p := p) V hV (j u₀) hz s G _).2
    fun g hg ↦ ?_
  apply monodromy_pullback_eq_one_of_mem_fixingSubgroup W.ι s G T
  have hl : IsOpenImmersion.lift V.ι (W.ι ≫ j) (by rwa [Scheme.Opens.range_ι]) ≫
      j.isoOpensRange.inv = W.ι := by
    rw [Iso.comp_inv_eq, ← cancel_mono V.ι, IsOpenImmersion.lift_fac, Category.assoc]
    exact congrArg (W.ι ≫ ·) (Scheme.Hom.isoOpensRange_hom_ι j).symm
  have := fixingSubgroup_le_comp s _ G j.isoOpensRange.inv hg
  rwa [hl] at this

/-- Blueprint `proposition-no-fixed-class-degree-one--1`: extension over finitely many points.

Let `U' ⊆ U` be nonempty opens of a smooth connected curve `C` over an algebraically closed
field. A `ℤ / N`-torsor on `U'` whose residues vanish at the points of `U ∖ U'` is the
restriction of a torsor on `U`. -/
theorem exists_isIsomorphic_pullback_of_residue_eq_zero {U' : Scheme.{u}} (ι : U' ⟶ U)
    [IsOpenImmersion ι] [Nonempty U'] [ConnectedSpace U'] {N : ℕ} [NeZero N] [NeZero (N : k)]
    (T : EtaleTorsor (ULift.{u + 1} (ZMod N)) U')
    (h : ∀ y ∈ Set.range j.base, y ∉ Set.range (ι ≫ j).base → T.residue (ι ≫ j) p y = 0) :
    ∃ T' : EtaleTorsor (ULift.{u + 1} (ZMod N)) U, (T'.pullback ι).IsIsomorphic T := by
  classical
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  have := irreducibleSpace_of_smooth (p := p)
  have hinj := j.isOpenEmbedding.injective
  obtain ⟨u'⟩ := (inferInstance : Nonempty U')
  -- a point of `U` outside `U'` maps to a point of `C` outside `U'`
  have hout {x : U} (hx : x ∉ Set.range ι.base) : j x ∉ Set.range (ι ≫ j).base := by
    rintro ⟨w, hw⟩
    exact hx ⟨w, hinj hw⟩
  have hfinU : (Set.range ι.base)ᶜ.Finite :=
    ((finite_boundary (p := p) (ι ≫ j)).preimage hinj.injOn).subset fun x hx ↦ hout hx
  let S : Finset U := hfinU.toFinset
  have hSU : (Set.range ι.base)ᶜ = ↑S := hfinU.coe_toFinset.symm
  have hmemS {z : U} (hz : z ∈ S) : z ∉ Set.range ι.base := by
    have : z ∈ (↑S : Set U) := hz
    rwa [← hSU] at this
  have hS : ∀ z ∈ S, IsClosed ({z} : Set U) := fun z hz ↦ by
    have hc : IsClosed ({j z} : Set C) :=
      (ι ≫ j).isOpenEmbedding.isOpen_range.isClosed_singleton_of_mem_compl
        (IsCurve.krullDim_le_one (f := p)) ⟨_, u', rfl⟩ (hout (hmemS hz))
    have : ({z} : Set U) = j.base ⁻¹' {j.base z} := by
      ext x
      simp [hinj.eq_iff]
    rw [this]
    exact hc.preimage j.base.hom.continuous
  have : IrreducibleSpace U := j.isOpenEmbedding.irreducibleSpace
  let s := (Etale.genericGeometricPoint (C := C) (ι ≫ j) : Spec (.of Ω) ⟶ _)
  obtain ⟨G, _, _⟩ := exists_isFundamentalGroup s
  have hV : ∀ z ∈ S, ConnectedSpace (complOpens S hS {z}).toScheme := fun z hz ↦ by
    have : Nonempty (complOpens S hS {z}).toScheme :=
      ⟨⟨ι u', range_le_complOpens ι S hS hSU {z} ⟨u', rfl⟩⟩⟩
    exact connectedSpace_of_isOpenImmersion (complOpens S hS {z}).ι
  have hconn : ∀ z ∈ S, ∀ P : (complOpens S hS {z}).toScheme.FiniteEtale, IsConnected P →
      IsConnected ((FiniteEtale.pullback (toComplOpens ι S hS hSU {z})).obj P) :=
      fun z hz P hP ↦ by
    have := hV z hz
    have := connectedSpace_of_isConnected P
    have : Etale P.obj.hom := P.obj.prop
    let q : P.obj.left ⟶ Spec (.of k) := P.obj.hom ≫ (complOpens S hS {z}).ι ≫ j ≫ p
    have : Smooth q := inferInstance
    have := LocallyOfFiniteType.isLocallyNoetherian q
    have := IsRegular.of_smooth q
    have := IsRegular.irreducibleSpace P.obj.left
    exact isConnected_pullback_of_irreducibleSpace _ P
  have hkill : ∀ g ∈ fixingSubgroup s ι G, T.monodromy s G g = 1 := by
    let K := (T.monodromy s G).toMonoidHom.ker
    have hKc : IsClosed (K : Set G) :=
      (isClosed_discrete {(1 : Multiplicative (ULift.{u + 1} (ZMod N)))}).preimage
        (T.monodromy s G).continuous
    have hle : (⨆ z : S, fixingSubgroup s (toComplOpens ι S hS hSU {z.1}) G) ≤ K :=
      iSup_le fun z g hg ↦ by
        let Wz := complOpens S hS {z.1}
        let V : C.Opens := j ''ᵁ Wz
        have hVr : Set.range (ι ≫ j).base ⊆ V := by
          rintro _ ⟨w, rfl⟩
          exact ⟨ι w, range_le_complOpens ι S hS hSU {z.1} ⟨w, rfl⟩, rfl⟩
        have hVz : (V : Set C) \ Set.range (ι ≫ j).base = {j z.1} := by
          ext x
          constructor
          · rintro ⟨⟨w, hw, rfl⟩, hx⟩
            have hw' : w ∉ Set.range ι.base := fun ⟨a, ha⟩ ↦ hx ⟨a, by
              rw [Scheme.Hom.comp_apply, ha]
              rfl⟩
            have hwS : w ∈ S := by
              have : w ∈ (↑S : Set U) := by rw [← hSU]; exact hw'
              exact this
            have hw2 : w ∉ S ∨ w ∈ ({z.1} : Finset U) := (mem_complOpens S hS).1 hw
            rcases hw2 with hw2 | hw2
            · exact absurd hwS hw2
            · rw [Finset.mem_singleton.1 hw2]
              rfl
          · rintro rfl
            refine ⟨⟨z.1, (mem_complOpens S hS).2 (Or.inr (Finset.mem_singleton_self _)), rfl⟩,
              hout (hmemS z.2)⟩
        have hres := (residue_eq_zero_iff_forall_monodromy_eq_one (p := p) V hVr (j z.1) hVz s
          G T).1 (h _ ⟨_, rfl⟩ (hout (hmemS z.2)))
        apply hres
        let m : Wz.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι (Wz.ι ≫ j) (by
          rw [Scheme.Opens.range_ι]
          rintro _ ⟨w, rfl⟩
          exact ⟨Wz.ι w, w.2, rfl⟩)
        have hm : toComplOpens ι S hS hSU {z.1} ≫ m =
            IsOpenImmersion.lift V.ι (ι ≫ j) (by rwa [Scheme.Opens.range_ι]) := by
          rw [← cancel_mono V.ι, IsOpenImmersion.lift_fac, Category.assoc,
            IsOpenImmersion.lift_fac, toComplOpens_ι_assoc]
        rw [← hm]
        exact fixingSubgroup_le_comp s _ G m hg
    intro g hg
    exact Subgroup.topologicalClosure_minimal _ hle hKc
      (fixingSubgroup_le_topologicalClosure_iSup ι S hS hSU s G hV hconn hg)
  have : Smooth (j ≫ p) := inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian (j ≫ p)
  have : IsRegular U := IsRegular.of_smooth (j ≫ p)
  obtain ⟨G', _, _⟩ := exists_isFundamentalGroup (s ≫ ι)
  exact exists_isIsomorphic_pullback ι s
    (fundamentalGroupMap_surjective_of_isRegular ι (pullbackFiberIso ι s) G G') T hkill

end Curve

end AlgebraicGeometry.Scheme.EtaleTorsor
