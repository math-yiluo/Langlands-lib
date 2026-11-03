import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Absolute.CocharacterDescentLattice
import Langlands.GroupScheme.Dynamic.BaseChange

/-! # Lattice base change for split tori -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace cocharacterLattice
variable {S S' : Scheme.{u}}

/-- The additive lattice map is the published dynamic cocharacter base change. -/
theorem groupHom_baseChange_dynamic (b : S' ⟶ S) (T : CommGroupScheme S)
    (ν : cocharacterLattice T) :
    CommGroupScheme.groupHom (baseChange b T ν) =
      Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν) := rfl

@[simp] theorem baseChange_comp (b : S' ⟶ S) {T U : CommGroupScheme S}
    (ν : cocharacterLattice T) (f : T ⟶ U) :
    baseChange b U (ν ≫ f) = baseChange b T ν ≫ (CommGroupScheme.baseChange b).map f := by
  simp [baseChange, Functor.map_comp]

end cocharacterLattice

namespace characterLattice
variable {S S' : Scheme.{u}}

@[simp] theorem baseChange_precomp (b : S' ⟶ S) {T U : CommGroupScheme S}
    (f : T ⟶ U) (χ : characterLattice U) :
    baseChange b T (f ≫ χ) = (CommGroupScheme.baseChange b).map f ≫ baseChange b U χ := by
  simp [baseChange, Functor.map_comp]
end characterLattice

/-- Change from an isomorphism of underlying groups to additive notation. -/
def CommGroupScheme.isoOfGroupIso {S : Scheme.{u}} {T U : CommGroupScheme S}
    (e : T.toGrp ≅ U.toGrp) : T ≅ U where
  hom := Additive.ofMul e.hom
  inv := Additive.ofMul e.inv
  hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
  inv_hom_id := congrArg Additive.ofMul e.inv_hom_id

section Endomorphisms
variable {k K : Type u} [CommRing k] [IsDomain k] [CommRing K] [IsDomain K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))

/-- The integer exponent of an endomorphism of `𝔾_m` is unchanged by base change. -/
theorem gmEndEquiv_baseChange (f : Gm (Spec (CommRingCat.of k)) ⟶ Gm (Spec (CommRingCat.of k))) :
    gmEndEquiv K ((Gm.commBaseChangeIso b).inv ≫
      (CommGroupScheme.baseChange b).map f ≫ (Gm.commBaseChangeIso b).hom) = gmEndEquiv k f := by
  conv_lhs => rw [eq_gmEndEquiv_zsmul k f]
  simp [gmEndEquiv_zsmul_id]

/-- The integer character/cocharacter pairing commutes with actual base change. -/
theorem latticePairing_baseChange (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (χ : characterLattice T) (ν : cocharacterLattice T) :
    latticePairing ((CommGroupScheme.baseChange b).obj T)
      (characterLattice.baseChange b T χ) (cocharacterLattice.baseChange b T ν) =
      latticePairing T χ ν := by
  change gmEndEquiv K _ = gmEndEquiv k _
  simpa [characterLattice.baseChange, cocharacterLattice.baseChange, Functor.map_comp,
    Category.assoc] using gmEndEquiv_baseChange b (ν ≫ χ)
end Endomorphisms

namespace splitTorus
variable {S S' : Scheme.{u}} (b : S' ⟶ S) (I : Type u) [Finite I]

/-- The canonical split-torus base-change isomorphism in additive notation. -/
def commBaseChangeIso :
    (CommGroupScheme.baseChange b).obj (commGroupScheme S I) ≅ commGroupScheme S' I :=
  CommGroupScheme.isoOfGroupIso (baseChangeIso b I)

/-- The canonical split-torus identification preserves every coordinate point. -/
theorem pointsEquiv_baseChangeIso_hom (U : Over S')
    (x : U ⟶ ((GroupScheme.baseChange b).obj (splitTorus S I)).X) :
    pointsEquiv I U (x ≫ (baseChangeIso b I).hom.hom.hom) = baseChangePointsEquiv b I U x := by
  exact isoOfPointModels_hom _ _ _ _ _ _ U x

/-- Every coordinate projection commutes with actual base change. -/
theorem commBaseChangeIso_hom_proj (i : I) :
    (commBaseChangeIso b I).hom ≫ proj S' I i =
      (CommGroupScheme.baseChange b).map (proj S I i) ≫ (Gm.commBaseChangeIso b).hom := by
  apply CommGroupScheme.hom_ext_points
  intro U x
  apply (Gm.pointsEquiv S' U).injective
  rw [comp_groupHom_comp, comp_proj]
  change pointsEquiv I U (x ≫ (baseChangeIso b I).hom.hom.hom) i = _
  rw [pointsEquiv_baseChangeIso_hom]
  change pointsEquiv I ((Over.map b).obj U) (GroupScheme.baseChangePointsEquiv b _ U x) i = _
  rw [comp_groupHom_comp]
  change _ = Gm.pointsEquiv S' U
    ((x ≫ ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom (proj S I i))).hom.hom) ≫
      (Gm.baseChangeIso b).hom.hom.hom)
  rw [Gm.pointsEquiv_baseChangeIso_hom, Gm.baseChangeUnitsEquiv_apply,
    GroupScheme.baseChangePointsEquiv_comp]
  rfl

section Domains
variable {k K : Type u} [CommRing k] [IsDomain k] [CommRing K] [IsDomain K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))

/-- Base change preserves the complete integral coordinate vector of an actual cocharacter. -/
theorem cocharacterLatticeEquiv_baseChange
    (ν : cocharacterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)) :
    cocharacterLatticeEquiv K I
      (cocharacterLattice.baseChange b _ ν ≫ (commBaseChangeIso b I).hom) =
      cocharacterLatticeEquiv k I ν := by
  funext i
  change gmEndEquiv K _ = gmEndEquiv k _
  rw [Category.assoc, commBaseChangeIso_hom_proj]
  change gmEndEquiv K ((Gm.commBaseChangeIso b).inv ≫
    (CommGroupScheme.baseChange b).map ν ≫
    (CommGroupScheme.baseChange b).map (proj _ I i) ≫ (Gm.commBaseChangeIso b).hom) = _
  rw [← Functor.map_comp_assoc, gmEndEquiv_baseChange]

/-- Pullback is bijective on the actual cocharacters of a coordinate split torus. -/
theorem cocharacterLattice_baseChange_bijective :
    Function.Bijective (cocharacterLattice.baseChange b
      (commGroupScheme (Spec (CommRingCat.of k)) I)) := by
  constructor
  · intro ν ν' h
    apply (cocharacterLatticeEquiv k I).injective
    rw [← cocharacterLatticeEquiv_baseChange I b ν,
      ← cocharacterLatticeEquiv_baseChange I b ν', h]
  · intro ν'
    let m := cocharacterLatticeEquiv K I (ν' ≫ (commBaseChangeIso b I).hom)
    refine ⟨(cocharacterLatticeEquiv k I).symm m, ?_⟩
    apply (cancel_mono (commBaseChangeIso b I).hom).1
    apply (cocharacterLatticeEquiv K I).injective
    rw [cocharacterLatticeEquiv_baseChange, AddEquiv.apply_symm_apply]

/-- A coordinate cocharacter pulls back to the same coordinate cocharacter. -/
theorem cocharacterLattice_baseChange_single (i : I) :
    cocharacterLattice.baseChange b _ (single (Spec (CommRingCat.of k)) I i) ≫
      (commBaseChangeIso b I).hom = single (Spec (CommRingCat.of K)) I i := by
  apply (cocharacterLatticeEquiv K I).injective
  rw [cocharacterLatticeEquiv_baseChange]
  funext j
  change gmEndEquiv k (single _ I i ≫ proj _ I j) =
    gmEndEquiv K (single _ I i ≫ proj _ I j)
  rw [single_comp_proj, single_comp_proj]
  split_ifs <;> simp

/-- Every character retains its complete integral coordinate vector under pullback. -/
theorem characterLatticeEquiv_baseChange
    (χ : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)) :
    characterLatticeEquiv K I
      ((commBaseChangeIso b I).inv ≫ characterLattice.baseChange b _ χ) =
      characterLatticeEquiv k I χ := by
  funext i
  change gmEndEquiv K _ = gmEndEquiv k _
  have hs := cocharacterLattice_baseChange_single I b i
  have hs' : single (Spec (CommRingCat.of K)) I i ≫ (commBaseChangeIso b I).inv =
      cocharacterLattice.baseChange b _ (single (Spec (CommRingCat.of k)) I i) := by
    rw [← hs]
    simp
  rw [← Category.assoc, hs']
  change gmEndEquiv K ((Gm.commBaseChangeIso b).inv ≫
    (CommGroupScheme.baseChange b).map (single _ I i) ≫
    (CommGroupScheme.baseChange b).map χ ≫ (Gm.commBaseChangeIso b).hom) = _
  rw [← Functor.map_comp_assoc, gmEndEquiv_baseChange]

/-- Pullback is bijective on the actual characters of a coordinate split torus. -/
theorem characterLattice_baseChange_bijective :
    Function.Bijective (characterLattice.baseChange b
      (commGroupScheme (Spec (CommRingCat.of k)) I)) := by
  constructor
  · intro χ ψ h
    apply (characterLatticeEquiv k I).injective
    rw [← characterLatticeEquiv_baseChange I b χ,
      ← characterLatticeEquiv_baseChange I b ψ, h]
  · intro χ'
    let m := characterLatticeEquiv K I ((commBaseChangeIso b I).inv ≫ χ')
    refine ⟨(characterLatticeEquiv k I).symm m, ?_⟩
    apply (cancel_epi (commBaseChangeIso b I).inv).1
    apply (characterLatticeEquiv K I).injective
    rw [characterLatticeEquiv_baseChange, AddEquiv.apply_symm_apply]

end Domains
end splitTorus
section SplitTori
variable {k K : Type u} [CommRing k] [IsDomain k] [CommRing K] [IsDomain K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus T.toGrp)

include hT

/-- Actual cocharacters of a split torus are unchanged under every base map between
integral-domain spectra. In particular this applies to arbitrary field extensions. -/
theorem IsSplitTorus.cocharacterLattice_baseChange_bijective :
    Function.Bijective (cocharacterLattice.baseChange b T) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let e' : T ≅ splitTorus.commGroupScheme _ I := CommGroupScheme.isoOfGroupIso e
  constructor
  · intro ν ν' h
    apply (cancel_mono e'.hom).1
    apply (splitTorus.cocharacterLattice_baseChange_bijective I b).injective
    simpa only [cocharacterLattice.baseChange_comp] using
      congrArg (fun θ => θ ≫ (CommGroupScheme.baseChange b).map e'.hom) h
  · intro ν'
    obtain ⟨ν, hν⟩ := (splitTorus.cocharacterLattice_baseChange_bijective I b).surjective
      (ν' ≫ (CommGroupScheme.baseChange b).map e'.hom)
    refine ⟨ν ≫ e'.inv, ?_⟩
    rw [cocharacterLattice.baseChange_comp, hν]
    simp [← Functor.map_comp, Category.assoc]

/-- Actual characters of a split torus are unchanged under every base map between
integral-domain spectra. In particular this applies to arbitrary field extensions. -/
theorem IsSplitTorus.characterLattice_baseChange_bijective :
    Function.Bijective (characterLattice.baseChange b T) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let e' : T ≅ splitTorus.commGroupScheme _ I := CommGroupScheme.isoOfGroupIso e
  constructor
  · intro χ ψ h
    apply (cancel_epi e'.inv).1
    apply (splitTorus.characterLattice_baseChange_bijective I b).injective
    simpa only [characterLattice.baseChange_precomp] using
      congrArg (fun θ => (CommGroupScheme.baseChange b).map e'.inv ≫ θ) h
  · intro χ'
    obtain ⟨χ, hχ⟩ := (splitTorus.characterLattice_baseChange_bijective I b).surjective
      ((CommGroupScheme.baseChange b).map e'.inv ≫ χ')
    refine ⟨e'.hom ≫ χ, ?_⟩
    rw [characterLattice.baseChange_precomp, hχ]
    simp [← Functor.map_comp, ← Category.assoc]

/-- Canonical equivalence on actual cocharacter lattices induced by pullback. -/
def cocharacterLattice.baseChangeEquiv :
    cocharacterLattice T ≃+ cocharacterLattice ((CommGroupScheme.baseChange b).obj T) :=
  AddEquiv.ofBijective (cocharacterLattice.baseChange b T)
    (hT.cocharacterLattice_baseChange_bijective b T)

@[simp] theorem cocharacterLattice.baseChangeEquiv_apply (ν : cocharacterLattice T) :
    cocharacterLattice.baseChangeEquiv b T hT ν = cocharacterLattice.baseChange b T ν := rfl

/-- Canonical equivalence on actual character lattices induced by pullback. -/
def characterLattice.baseChangeEquiv :
    characterLattice T ≃+ characterLattice ((CommGroupScheme.baseChange b).obj T) :=
  AddEquiv.ofBijective (characterLattice.baseChange b T)
    (hT.characterLattice_baseChange_bijective b T)

@[simp] theorem characterLattice.baseChangeEquiv_apply (χ : characterLattice T) :
    characterLattice.baseChangeEquiv b T hT χ = characterLattice.baseChange b T χ := rfl

/-- A cocharacter of the scalar-extended split torus has a unique actual cocharacter
of the original torus whose dynamic base change equals it. -/
theorem IsSplitTorus.existsUnique_baseChangeCocharacter
    (ν' : ((Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange b).obj T.toGrp)) :
    ∃! ν : cocharacterLattice T,
      Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν) = ν' := by
  obtain ⟨ν, hν⟩ := (hT.cocharacterLattice_baseChange_bijective b T).surjective
    (Additive.ofMul ν')
  refine ⟨ν, congrArg CommGroupScheme.groupHom hν, ?_⟩
  intro ν₀ hν₀
  apply (hT.cocharacterLattice_baseChange_bijective b T).injective
  apply Additive.toMul.injective
  exact hν₀.trans (congrArg CommGroupScheme.groupHom hν).symm

end SplitTori

end Langlands.GroupScheme
