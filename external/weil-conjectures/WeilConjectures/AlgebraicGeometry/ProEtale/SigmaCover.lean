/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine

/-!
# Finite disjoint unions in the affine pro-étale site

Let `f i : V i ⟶ X` be a finite family of morphisms in the affine pro-étale site `S.AffineProEt`.
The spectrum `Spec (∏ᵢ Γ(V i))` is the disjoint union of the `V i` and is again an object of the
affine pro-étale site (`AlgebraicGeometry.Scheme.AffineProEt.sigmaCover`), mapping to `X`. Its
components `V i ⟶ Spec (∏ᵢ Γ(V i))` are pairwise disjoint open immersions covering it.

## Main statements

* `AlgebraicGeometry.Scheme.AffineProEt.zariskiTopology_le_topology`: the Zariski topology on
  the affine pro-étale site is coarser than the pro-étale topology.
* `AlgebraicGeometry.Scheme.AffineProEt.subsingleton_of_isEmpty`: a sheaf has at most one section
  over an empty object.
* `AlgebraicGeometry.Scheme.AffineProEt.exists_sigmaCover_glue`: sections of a sheaf over the
  `V i` glue to a section over the disjoint union.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.AffineProEt

variable {S : Scheme.{u}}

variable (S) in
/-- The Zariski topology on the affine pro-étale site is coarser than the pro-étale topology. -/
lemma zariskiTopology_le_topology : zariskiTopology S ≤ topology S := by
  rw [zariskiTopology_eq_toGrothendieck_zariskiPrecoverage,
    Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
  intro X R hR
  simp only [topology, GrothendieckTopology.mem_toPrecoverage_iff]
  apply Functor.mem_restrictedTopology_of_functorPushforward_mem
  rw [ProEt.topology, ← Sieve.generate_map_eq_functorPushforward]
  refine Precoverage.generate_mem_toGrothendieck ?_
  simp only [ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_comp]
  simp only [zariskiPrecoverage, Precoverage.mem_comap_iff, Presieve.map_comp] at hR
  exact zariskiPrecoverage_le_propQCPrecoverage _ hR

/-- A jointly surjective family of open immersions in the affine pro-étale site generates a
covering sieve for the pro-étale topology. -/
lemma generate_mem_topology {X : S.AffineProEt} {ι : Type*} {V : ι → S.AffineProEt}
    (g : ∀ i, V i ⟶ X) (hoi : ∀ i, IsOpenImmersion (g i).left)
    (hsurj : ∀ x : X.left, ∃ i, x ∈ Set.range ((g i).left.base)) :
    Sieve.generate (Presieve.ofArrows V g) ∈ topology S X :=
  zariskiTopology_le_topology S _ (generate_mem_zariskiTopology g hoi hsurj)

/-- A sheaf of types on the affine pro-étale site has at most one section over an object with
empty underlying scheme: the empty family is a covering. -/
lemma subsingleton_of_isEmpty {F : S.AffineProEtᵒᵖ ⥤ Type w}
    (hF : Presheaf.IsSheaf (topology S) F) {X : S.AffineProEt} (hX : IsEmpty X.left) :
    Subsingleton (F.obj (op X)) := by
  let V : PEmpty.{u + 2} → S.AffineProEt := PEmpty.elim
  let g : ∀ i, V i ⟶ X := fun i ↦ i.elim
  have hsep : (Presieve.ofArrows V g).IsSeparatedFor F :=
    ((Presieve.isSheafFor_iff_generate _).mpr ((isSheaf_iff_isSheaf_of_type _ _).mp hF _
      (generate_mem_topology g (fun i ↦ i.elim) fun x ↦ hX.elim x))).isSeparatedFor
  refine ⟨fun t₁ t₂ ↦ hsep.ext ?_⟩
  rintro Y h ⟨i⟩
  exact i.elim

end AlgebraicGeometry.Scheme.AffineProEt

namespace AlgebraicGeometry.Scheme.AffineProEt

variable {S : Scheme.{u}} {X : S.AffineProEt} {ι : Type u} [Finite ι] (V : ι → S.AffineProEt)
  (f : ∀ i, V i ⟶ X)

/-- The ring map `Γ(X) ⟶ ∏ᵢ Γ(V i)` induced by a family `f i : V i ⟶ X`. -/
noncomputable def sigmaRingHom : Γ(X.left, ⊤) ⟶ CommRingCat.of (Π i, Γ((V i).left, ⊤)) :=
  CommRingCat.ofHom (RingHom.pi fun i ↦ ((f i).left.appTop).hom)

/-- The structure morphism of the disjoint union `Spec (∏ᵢ Γ(V i)) ⟶ X` is pro-affine-étale. -/
lemma proAffineEtale_sigmaCover :
    proAffineEtale (Spec.map (sigmaRingHom V f) ≫ X.left.isoSpec.inv) :=
  (MorphismProperty.cancel_right_of_respectsIso _ _ _).mpr (proAffineEtale_Spec_iff.mpr
    (RingHom.IndEtale.pi _ fun i ↦ indEtale_appTop_of_proAffineEtale (proAffineEtale_hom (f i))))

/-- The disjoint union `Spec (∏ᵢ Γ(V i))` of a finite family `f i : V i ⟶ X` in the affine
pro-étale site, as an object over `X`. -/
noncomputable def sigmaCover : S.AffineProEt :=
  mk ((Spec.map (sigmaRingHom V f) ≫ X.left.isoSpec.inv) ≫ X.hom)
    (proAffineEtale.comp_mem _ _ (proAffineEtale_sigmaCover V f) X.prop)

/-- The projection from the disjoint union `Spec (∏ᵢ Γ(V i))` to `X`. -/
noncomputable def sigmaCoverπ : sigmaCover V f ⟶ X :=
  MorphismProperty.Over.homMk (Spec.map (sigmaRingHom V f) ≫ X.left.isoSpec.inv) rfl trivial

/-- The underlying morphism of schemes of the inclusion `V i ⟶ Spec (∏ᵢ Γ(V i))`. -/
noncomputable def sigmaCoverιLeft (i : ι) : (V i).left ⟶ Spec (.of (Π i, Γ((V i).left, ⊤))) :=
  (V i).left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i))

omit [Finite ι] in
lemma sigmaCoverιLeft_comp (i : ι) :
    sigmaCoverιLeft V i ≫ Spec.map (sigmaRingHom V f) ≫ X.left.isoSpec.inv = (f i).left := by
  have h1 : sigmaRingHom V f ≫ CommRingCat.ofHom (Pi.evalRingHom _ i) = (f i).left.appTop := by
    ext x
    rfl
  rw [sigmaCoverιLeft, Category.assoc, ← Spec.map_comp_assoc, h1,
    Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The inclusion `V i ⟶ Spec (∏ᵢ Γ(V i))` of a component of the disjoint union. -/
noncomputable def sigmaCoverι (i : ι) : V i ⟶ sigmaCover V f :=
  MorphismProperty.Over.homMk (sigmaCoverιLeft V i) (by
    simp only [sigmaCover, mk_hom]
    rw [← Category.assoc, sigmaCoverιLeft_comp, MorphismProperty.Over.w (f i)]) trivial

@[simp]
lemma sigmaCoverι_left (i : ι) : (sigmaCoverι V f i).left = sigmaCoverιLeft V i :=
  rfl

@[reassoc (attr := simp)]
lemma sigmaCoverι_π (i : ι) : sigmaCoverι V f i ≫ sigmaCoverπ V f = f i :=
  MorphismProperty.Over.Hom.ext (sigmaCoverιLeft_comp V f i)

/-- The components of the disjoint union are open immersions. -/
lemma isOpenImmersion_sigmaCoverι (i : ι) : IsOpenImmersion (sigmaCoverι V f i).left := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) i))) := by
    rw [← ι_sigmaSpec (fun k ↦ Γ((V k).left, ⊤)) i]
    infer_instance
  rw [sigmaCoverι_left, sigmaCoverιLeft]
  infer_instance

/-- The disjoint union of a jointly surjective family surjects onto the target. -/
lemma surjective_sigmaCoverπ (hsurj : ∀ x : X.left, ∃ i, x ∈ Set.range ((f i).left.base)) :
    Surjective (sigmaCoverπ V f).left := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨i, y, rfl⟩ := hsurj x
  refine ⟨(sigmaCoverι V f i).left y, ?_⟩
  rw [← sigmaCoverι_π V f i]
  rfl

/-- The components `V i ⟶ Spec (∏ᵢ Γ(V i))` cover the disjoint union. -/
lemma exists_mem_range_sigmaCoverι (w : (sigmaCover V f).left) :
    ∃ i, w ∈ Set.range (sigmaCoverι V f i).left.base := by
  obtain ⟨p, rfl⟩ := (sigmaSpec fun i ↦ Γ((V i).left, ⊤)).surjective w
  obtain ⟨y, hy⟩ := (sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).covers p
  generalize (sigmaOpenCover fun k ↦ Spec (Γ((V k).left, ⊤))).idx p = i at y hy
  subst hy
  refine ⟨i, (V i).left.isoSpec.inv y, ?_⟩
  rw [sigmaCoverι_left, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, sigmaCoverιLeft,
    Iso.inv_hom_id_assoc, ← ι_sigmaSpec]
  rfl

/-- Distinct components of the disjoint union are disjoint: an object mapping compatibly to two
distinct components is empty. -/
lemma isEmpty_of_sigmaCoverι_eq {i j : ι} (hij : i ≠ j) {Q : S.AffineProEt} (g : Q ⟶ V i)
    (g' : Q ⟶ V j) (h : g ≫ sigmaCoverι V f i = g' ≫ sigmaCoverι V f j) : IsEmpty Q.left := by
  classical
  refine ⟨fun x ↦ ?_⟩
  have hx : (g ≫ sigmaCoverι V f i).left x = (g' ≫ sigmaCoverι V f j).left x := by rw [h]
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left] at hx
  simp only [Scheme.Hom.comp_apply, sigmaCoverι_left, sigmaCoverιLeft] at hx
  have key (k : ι) (z : PrimeSpectrum Γ((V k).left, ⊤)) :
      Pi.single i 1 ∈ ((Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun k ↦ (Γ((V k).left, ⊤) : Type u)) k))) z).asIdeal ↔
        (Pi.single i 1 : Π k, Γ((V k).left, ⊤)) k ∈ z.asIdeal :=
    Iff.rfl
  have h2 := (key i _).symm.trans
    ((Iff.of_eq (congr_arg (fun p : PrimeSpectrum _ ↦ Pi.single i 1 ∈ p.asIdeal) hx)).trans
      (key j _))
  rw [Pi.single_eq_same, Pi.single_eq_of_ne' hij] at h2
  exact Ideal.IsPrime.ne_top' (Ideal.eq_top_iff_one _ |>.mpr (h2.mpr (Ideal.zero_mem _)))

/-- The components of the disjoint union are monomorphisms. -/
instance (i : ι) : Mono (sigmaCoverι V f i) := by
  refine ⟨fun g g' h ↦ MorphismProperty.Over.Hom.ext ?_⟩
  have := isOpenImmersion_sigmaCoverι V f i
  have hl : (g ≫ sigmaCoverι V f i).left = (g' ≫ sigmaCoverι V f i).left := by rw [h]
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left] at hl
  exact (cancel_mono _).mp hl

/-- Sections of a sheaf over the components `V i` glue to a section over the disjoint union. -/
lemma exists_sigmaCover_glue {F : S.AffineProEtᵒᵖ ⥤ Type w}
    (hF : Presheaf.IsSheaf (topology S) F) (x : ∀ i, F.obj (op (V i))) :
    ∃ z : F.obj (op (sigmaCover V f)), ∀ i, F.map (sigmaCoverι V f i).op z = x i := by
  have hsh : (Presieve.ofArrows V (sigmaCoverι V f)).IsSheafFor F :=
    (Presieve.isSheafFor_iff_generate _).mpr ((isSheaf_iff_isSheaf_of_type _ _).mp hF _
      (generate_mem_topology _ (isOpenImmersion_sigmaCoverι V f)
        (exists_mem_range_sigmaCoverι V f)))
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  obtain ⟨z, hz, -⟩ := hsh x fun a b Q ga gb hab ↦ by
    by_cases h : a = b
    · subst h
      obtain rfl := (cancel_mono _).mp hab
      rfl
    · have := subsingleton_of_isEmpty hF (isEmpty_of_sigmaCoverι_eq V f h ga gb hab)
      exact Subsingleton.elim _ _
  exact ⟨z, hz⟩

/-- Two sections of a sheaf over the disjoint union agree if they agree on every component. -/
lemma sigmaCover_ext {F : S.AffineProEtᵒᵖ ⥤ Type w} (hF : Presheaf.IsSheaf (topology S) F)
    {z z' : F.obj (op (sigmaCover V f))}
    (h : ∀ i, F.map (sigmaCoverι V f i).op z = F.map (sigmaCoverι V f i).op z') : z = z' := by
  have hsep : (Presieve.ofArrows V (sigmaCoverι V f)).IsSeparatedFor F :=
    ((Presieve.isSheafFor_iff_generate _).mpr ((isSheaf_iff_isSheaf_of_type _ _).mp hF _
      (generate_mem_topology _ (isOpenImmersion_sigmaCoverι V f)
        (exists_mem_range_sigmaCoverι V f)))).isSeparatedFor
  refine hsep.ext ?_
  rintro Y g ⟨i⟩
  exact h i

end AlgebraicGeometry.Scheme.AffineProEt
