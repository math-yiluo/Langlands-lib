import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

/-! # From a classifier of closed subschemes over affine tests to a universal ideal sheaf

Let `f : X ⟶ Spec A` and `πH : H ⟶ Spec A`. Suppose that every closed subscheme of
`X ×_A Spec S'`, flat and locally of finite presentation over `Spec S'`, has a classifying
morphism `Spec S' ⟶ H` over `Spec A`, compatible with base change and surjective, and that a
closed subscheme `𝒵` of `X ×_A H` pulls back to each classified subscheme. Then the kernel `W`
of `𝒵 ⟶ X ×_A H` classifies, by pulling back, the ideal sheaves on `X ×_A T` with flat and
locally finitely presented closed subscheme, for every scheme `T`. The affine case is the
classifier itself; the general case glues along an affine open cover of `T`. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

noncomputable section

namespace Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamily

section Kernel

/-- In a pullback square whose right side is a closed immersion, the kernel of the left side is
the pullback of the kernel of the right side. -/
lemma ker_eq_comap_of_isPullback {Z' P' Z P : Scheme.{u}} {ι' : Z' ⟶ P'} {e : Z' ⟶ Z}
    {h : P' ⟶ P} {ι : Z ⟶ P} [IsClosedImmersion ι] (sq : IsPullback ι' e h ι) :
    ι'.ker = ι.ker.comap h := by
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- The closed subscheme of a pulled-back ideal sheaf sits in a pullback square. -/
lemma isPullback_comap {Y' Y : Scheme.{u}} (h : Y' ⟶ Y) (I : Y.IdealSheafData) :
    IsPullback (I.comap h).subschemeι ((I.comapIso h).hom ≫ pullback.snd _ _) h
      I.subschemeι :=
  IsPullback.of_iso_pullback
    ⟨by rw [← I.comapIso_hom_fst h, Category.assoc, pullback.condition, Category.assoc]⟩
    (I.comapIso h) (I.comapIso_hom_fst h) rfl

/-- Ideal sheaves whose pullbacks along a jointly surjective family of open immersions agree
are equal. -/
lemma eq_of_comap_eq {Y : Scheme.{u}} {ι : Type*} {V : ι → Scheme.{u}} (m : ∀ i, V i ⟶ Y)
    [∀ i, IsOpenImmersion (m i)] (hm : ⨆ i, (m i).opensRange = ⊤)
    {I J : Y.IdealSheafData} (h : ∀ i, I.comap (m i) = J.comap (m i)) : I = J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun p : Σ i, (V i).affineOpens => ⟨m p.1 ''ᵁ p.2.1, p.2.2.image_of_isOpenImmersion _⟩)
    ?_ ?_
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨i, y, rfl⟩ : ∃ i, x ∈ Set.range (m i) :=
      TopologicalSpace.Opens.mem_iSup.mp (hm.ge (Set.mem_univ x))
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top (V i)).ge (Set.mem_univ y))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, U⟩, ⟨y, hU, rfl⟩⟩
  · rintro ⟨i, U⟩
    have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I (m i) U
    have h2 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion J (m i) U
    rw [h i] at h1
    exact Ideal.comap_injective_of_surjective _
      (ConcreteCategory.bijective_of_isIso ((m i).appIso U).inv).2 (h1.symm.trans h2)

end Kernel

section Families

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The map `X ×_S T' ⟶ X ×_S T` induced by a morphism `T' ⟶ T` over `S`. -/
abbrev mapX {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T) (w : h ≫ s = s') :
    pullback f s' ⟶ pullback f s :=
  pullback.map f s' f s (𝟙 X) h (𝟙 _) (by simp) (by simp [w])

@[reassoc]
lemma mapX_fst {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T) (w : h ≫ s = s') :
    mapX f h w ≫ pullback.fst f s = pullback.fst f s' :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
lemma mapX_snd {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T) (w : h ≫ s = s') :
    mapX f h w ≫ pullback.snd f s = pullback.snd f s' ≫ h :=
  pullback.lift_snd _ _ _

lemma isPullback_mapX {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T)
    (w : h ≫ s = s') :
    IsPullback (mapX f h w) (pullback.snd f s') (pullback.snd f s) h := by
  subst w
  refine IsPullback.of_right ?_ (mapX_snd f h rfl) (IsPullback.of_hasPullback f s)
  rw [mapX_fst]
  exact IsPullback.of_hasPullback f (h ≫ s)

lemma mapX_comp {T T' T'' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} {s'' : T'' ⟶ S}
    (h : T' ⟶ T) (w : h ≫ s = s') (h' : T'' ⟶ T') (w' : h' ≫ s' = s'') :
    mapX f h' w' ≫ mapX f h w = mapX f (h' ≫ h) (by rw [Category.assoc, w, w']) := by
  apply pullback.hom_ext
  · rw [Category.assoc, mapX_fst, mapX_fst, mapX_fst]
  · rw [Category.assoc, mapX_snd, mapX_snd_assoc, mapX_snd]

lemma mapX_congr {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} {h₁ h₂ : T' ⟶ T}
    (w₁ : h₁ ≫ s = s') (w₂ : h₂ ≫ s = s') (e : h₁ = h₂) : mapX f h₁ w₁ = mapX f h₂ w₂ := by
  subst e
  rfl

lemma comap_mapX_comap_mapX {T T' T'' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} {s'' : T'' ⟶ S}
    (J : (pullback f s).IdealSheafData) (h : T' ⟶ T) (w : h ≫ s = s') (h' : T'' ⟶ T')
    (w' : h' ≫ s' = s'') :
    (J.comap (mapX f h w)).comap (mapX f h' w') =
      J.comap (mapX f (h' ≫ h) (by rw [Category.assoc, w, w'])) := by
  rw [← Scheme.IdealSheafData.comap_comp, mapX_comp]

/-- Flatness and local finite presentation of the closed subscheme of an ideal sheaf on
`X ×_S T` over `T` pass to its pullback to `X ×_S T'`. -/
lemma flat_lfp_comap {T T' : Scheme.{u}} {s : T ⟶ S} {s' : T' ⟶ S} (h : T' ⟶ T)
    (w : h ≫ s = s') (I : (pullback f s).IdealSheafData)
    (hfl : Flat (I.subschemeι ≫ pullback.snd f s))
    (hfp : LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd f s)) :
    Flat ((I.comap (mapX f h w)).subschemeι ≫ pullback.snd f s') ∧
      LocallyOfFinitePresentation ((I.comap (mapX f h w)).subschemeι ≫ pullback.snd f s') := by
  have sq := (isPullback_comap (mapX f h w) I).flip.paste_vert (isPullback_mapX f h w)
  exact ⟨MorphismProperty.of_isPullback (P := @Flat) sq hfl,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sq hfp⟩

/-- The maps `X ×_S Uᵢ ⟶ X ×_S T` for an open cover `Uᵢ` of `T` are open immersions. -/
lemma isOpenImmersion_mapX {T T' : Scheme.{u}} {s : T ⟶ S} (h : T' ⟶ T) [IsOpenImmersion h] :
    IsOpenImmersion (mapX f h (s' := h ≫ s) rfl) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_mapX f h rfl).flip ‹_›

/-- For a jointly surjective family of morphisms `jᵢ : Vᵢ ⟶ T`, the maps
`X ×_S Vᵢ ⟶ X ×_S T` are jointly surjective. -/
lemma iSup_opensRange_mapX {T : Scheme.{u}} (s : T ⟶ S) {ι : Type*} {V : ι → Scheme.{u}}
    (j : ∀ i, V i ⟶ T) [∀ i, IsOpenImmersion (j i)] (hj : ∀ x : T, ∃ i y, j i y = x) :
    ⨆ i, (mapX f (j i) (s := s) rfl).opensRange = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨i, y, hy⟩ := hj (pullback.snd f s x)
  have hx : x ∈ Set.range (pullback.fst (pullback.snd f s) (j i)) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨y, hy⟩
  obtain ⟨z, rfl⟩ := hx
  have := isOpenImmersion_mapX f (s := s) (j i)
  refine TopologicalSpace.Opens.mem_iSup.mpr
    ⟨i, ⟨(isPullback_mapX f (j i) (s := s) rfl).isoPullback.inv z, ?_⟩⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]

end Families

/-- `Spec Γ(T, U) ⟶ T` is an open immersion, for `U` in `T.affineOpens` (instance search does
not see `U.2` as a proof of `IsAffineOpen U`). -/
lemma isOpenImmersion_affineOpens_fromSpec {T : Scheme.{u}} (U : T.affineOpens) :
    IsOpenImmersion U.2.fromSpec :=
  IsAffineOpen.isOpenImmersion_fromSpec U.2

attribute [local instance] isOpenImmersion_affineOpens_fromSpec

/-- Every point of `T` lies in the image of `Spec Γ(T, U) ⟶ T` for some affine open `U`. -/
lemma exists_fromSpec_eq {T : Scheme.{u}} (x : T) :
    ∃ (U : T.affineOpens) (y : Spec Γ(T, U)), U.2.fromSpec y = x := by
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top T).ge (Set.mem_univ x))
  have hx : x ∈ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]
    exact hU
  obtain ⟨y, hy⟩ := hx
  exact ⟨U, y, hy⟩

/-- The open cover of `T` by the morphisms `Spec Γ(T, U) ⟶ T`, for `U` affine open. -/
abbrev affineFromSpecCover (T : Scheme.{u}) : T.OpenCover :=
  Scheme.Cover.mkOfCovers T.affineOpens (fun U => Spec Γ(T, U)) (fun U => U.2.fromSpec)
    exists_fromSpec_eq

section Classifier

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  {H : Scheme.{u}} (πH : H ⟶ Spec (CommRingCat.of A))
  (pt : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of A))
    (Z : Scheme.{u}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
      LocallyOfFinitePresentation (ι ≫ pullback.snd f s) → SchemeHomOver s πH)
  {𝒵 : Scheme.{u}} (ι : 𝒵 ⟶ pullback f πH)

/-- Compatibility of the classifier with base change along ring maps; this is the hypothesis
`hnat` of the Hilbert scheme theorems ported from the FLT project. -/
abbrev ClassifierNat : Prop :=
  ∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of A))
    (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of A))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
    (Z : Scheme.{u}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι)
    (hfl : Flat (ι ≫ pullback.snd f s))
    (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
    (Z'' : Scheme.{u}) (ι'' : Z'' ⟶ pullback f s'') (hι'' : IsClosedImmersion ι'')
    (hfl'' : Flat (ι'' ≫ pullback.snd f s''))
    (hfp'' : LocallyOfFinitePresentation (ι'' ≫ pullback.snd f s''))
    (e : Z'' ⟶ Z),
    IsPullback e (ι'' ≫ pullback.snd f s'') (ι ≫ pullback.snd f s)
      (Spec.map (CommRingCat.ofHom ψ)) →
    ι'' ≫ pullback.map f s'' f s (𝟙 X) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
        (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs]) = e ≫ ι →
    (pt S'' s'' Z'' ι'' hι'' hfl'' hfp'').1 =
      Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s Z ι hι hfl hfp).1

/-- Every morphism `Spec S' ⟶ H` over `Spec A` classifies some closed subscheme. -/
abbrev ClassifierSurj : Prop :=
  ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of A))
    (x : SchemeHomOver s πH),
    ∃ (Z : Scheme.{u}) (ιZ : Z ⟶ pullback f s) (hι : IsClosedImmersion ιZ)
      (hfl : Flat (ιZ ≫ pullback.snd f s))
      (hfp : LocallyOfFinitePresentation (ιZ ≫ pullback.snd f s)),
      pt S' s Z ιZ hι hfl hfp = x

/-- The closed subscheme `𝒵` of `X ×_A H` pulls back to every classified closed subscheme. -/
abbrev ClassifierUniv : Prop :=
  ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of A))
    (Z : Scheme.{u}) (ιZ : Z ⟶ pullback f s) (hι : IsClosedImmersion ιZ)
    (hfl : Flat (ιZ ≫ pullback.snd f s))
    (hfp : LocallyOfFinitePresentation (ιZ ≫ pullback.snd f s)),
    ∃ e : Z ⟶ 𝒵,
      IsPullback e (ιZ ≫ pullback.snd f s) (ι ≫ pullback.snd f πH)
        (pt S' s Z ιZ hι hfl hfp).1 ∧
      ιZ ≫ pullback.map f s f πH (𝟙 X) (pt S' s Z ιZ hι hfl hfp).1 (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp])
          (by rw [Category.comp_id, (pt S' s Z ιZ hι hfl hfp).2]) = e ≫ ι

variable {f πH pt} in
/-- The classifier is invariant under isomorphisms of closed subschemes over `X ×_A Spec S'`;
this is base-change compatibility along the identity. -/
lemma pt_eq_of_iso (hnat : ClassifierNat f πH pt)
    {S' : Type u} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of A))
    {Z₁ Z₂ : Scheme.{u}} (ι₁ : Z₁ ⟶ pullback f s) (ι₂ : Z₂ ⟶ pullback f s)
    (h₁ : IsClosedImmersion ι₁) (h₂ : IsClosedImmersion ι₂)
    (fl₁ : Flat (ι₁ ≫ pullback.snd f s)) (fl₂ : Flat (ι₂ ≫ pullback.snd f s))
    (fp₁ : LocallyOfFinitePresentation (ι₁ ≫ pullback.snd f s))
    (fp₂ : LocallyOfFinitePresentation (ι₂ ≫ pullback.snd f s))
    (e : Z₁ ⟶ Z₂) [IsIso e] (he : e ≫ ι₂ = ι₁) :
    (pt S' s Z₁ ι₁ h₁ fl₁ fp₁).1 = (pt S' s Z₂ ι₂ h₂ fl₂ fp₂).1 := by
  have key : Spec.map (CommRingCat.ofHom (RingHom.id S')) = 𝟙 _ := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
  have hs : Spec.map (CommRingCat.ofHom (RingHom.id S')) ≫ s = s := by
    rw [key, Category.id_comp]
  have hm : pullback.map f s f s (𝟙 X) (Spec.map (CommRingCat.ofHom (RingHom.id S'))) (𝟙 _)
      (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs]) = 𝟙 _ := by
    apply pullback.hom_ext <;> simp
  have := hnat S' S' (RingHom.id S') s s hs Z₂ ι₂ h₂ fl₂ fp₂ Z₁ ι₁ h₁ fl₁ fp₁ e ?_ ?_
  · rw [this, key, Category.id_comp]
  · rw [key]
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.comp_id, ← he, Category.assoc]
  · rw [hm, Category.comp_id, he]

variable [IsClosedImmersion ι]

variable {f πH pt ι} in
/-- Over an affine test, the pullback of the kernel of `ι` along the classifying morphism of a
closed subscheme is the ideal sheaf of that subscheme. -/
lemma comap_mapX_pt (huniv : ClassifierUniv f πH pt ι)
    {S' : Type u} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of A))
    (Z : Scheme.{u}) (ιZ : Z ⟶ pullback f s) (hι : IsClosedImmersion ιZ)
    (hfl : Flat (ιZ ≫ pullback.snd f s))
    (hfp : LocallyOfFinitePresentation (ιZ ≫ pullback.snd f s)) :
    ι.ker.comap (mapX f (pt S' s Z ιZ hι hfl hfp).1 (pt S' s Z ιZ hι hfl hfp).2) = ιZ.ker := by
  obtain ⟨e, sq, he⟩ := huniv S' s Z ιZ hι hfl hfp
  have sq' := IsPullback.of_bot sq he.symm
    (isPullback_mapX f (pt S' s Z ιZ hι hfl hfp).1 (pt S' s Z ιZ hι hfl hfp).2)
  exact (ker_eq_comap_of_isPullback sq'.flip).symm

variable {f πH pt ι} in
/-- Over an affine test, a morphism to `H` along which the kernel of `ι` pulls back to an ideal
sheaf `I` is the classifying morphism of the closed subscheme of `I`. -/
lemma eq_pt (hnat : ClassifierNat f πH pt) (hsurj : ClassifierSurj f πH pt)
    (huniv : ClassifierUniv f πH pt ι)
    {S' : Type u} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of A))
    (g : Spec (CommRingCat.of S') ⟶ H) (hg : g ≫ πH = s)
    (I : (pullback f s).IdealSheafData) (hfl : Flat (I.subschemeι ≫ pullback.snd f s))
    (hfp : LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd f s))
    (hI : ι.ker.comap (mapX f g hg) = I) :
    g = (pt S' s I.subscheme I.subschemeι inferInstance hfl hfp).1 := by
  obtain ⟨Z, ιZ, hι, hfl', hfp', hpt⟩ := hsurj S' s ⟨g, hg⟩
  have h1 := comap_mapX_pt huniv s Z ιZ hι hfl' hfp'
  rw [hpt] at h1
  have h2 : ιZ.ker = I.subschemeι.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← hI]
    exact h1.symm
  have := hι
  have := IsClosedImmersion.isIso_lift I.subschemeι ιZ h2.symm
  exact (congrArg Subtype.val hpt).symm.trans (pt_eq_of_iso hnat s ιZ I.subschemeι hι
    inferInstance hfl' hfl hfp' hfp (IsClosedImmersion.lift I.subschemeι ιZ h2.symm.le)
    (IsClosedImmersion.lift_fac _ _ _))

variable {f πH ι} in
/-- The kernel of `ι` is flat and locally of finite presentation over `H` when `𝒵` is. -/
lemma flat_lfp_ker (hfl : Flat (ι ≫ pullback.snd f πH))
    (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f πH)) :
    Flat (ι.ker.subschemeι ≫ pullback.snd f πH) ∧
      LocallyOfFinitePresentation (ι.ker.subschemeι ≫ pullback.snd f πH) := by
  have e : ι.ker.subschemeι = inv ι.toImage ≫ ι := by
    rw [IsIso.eq_inv_comp]
    exact ι.toImage_imageι
  rw [e, Category.assoc]
  exact ⟨inferInstance, inferInstance⟩

variable {f πH pt ι} in
/-- Two morphisms `T ⟶ H` over `Spec A` along which the kernel of `ι` pulls back to the same
ideal sheaf are equal: they agree on an affine open cover of `T` by `eq_pt`. -/
lemma eq_of_comap_eq_comap (hnat : ClassifierNat f πH pt) (hsurj : ClassifierSurj f πH pt)
    (huniv : ClassifierUniv f πH pt ι)
    (hW : Flat (ι.ker.subschemeι ≫ pullback.snd f πH) ∧
      LocallyOfFinitePresentation (ι.ker.subschemeι ≫ pullback.snd f πH))
    {T : Scheme.{u}} {s : T ⟶ Spec (CommRingCat.of A)} (g₁ g₂ : T ⟶ H)
    (h₁ : g₁ ≫ πH = s) (h₂ : g₂ ≫ πH = s)
    (h : ι.ker.comap (mapX f g₁ h₁) = ι.ker.comap (mapX f g₂ h₂)) : g₁ = g₂ := by
  refine (affineFromSpecCover T).hom_ext _ _ fun (U : T.affineOpens) => ?_
  change U.2.fromSpec ≫ g₁ = U.2.fromSpec ≫ g₂
  have hW₁ := flat_lfp_comap f g₁ h₁ _ hW.1 hW.2
  have hI := flat_lfp_comap f U.2.fromSpec (s' := U.2.fromSpec ≫ s) rfl _ hW₁.1 hW₁.2
  have e₁ := comap_mapX_comap_mapX f ι.ker g₁ h₁ U.2.fromSpec rfl
  have e₂ := comap_mapX_comap_mapX f ι.ker g₂ h₂ U.2.fromSpec rfl
  have k₁ := eq_pt hnat hsurj huniv (S' := Γ(T, U)) (U.2.fromSpec ≫ s) (U.2.fromSpec ≫ g₁)
    (by rw [Category.assoc, h₁]) _ hI.1 hI.2 e₁.symm
  have k₂ := eq_pt hnat hsurj huniv (S' := Γ(T, U)) (U.2.fromSpec ≫ s) (U.2.fromSpec ≫ g₂)
    (by rw [Category.assoc, h₂]) _ hI.1 hI.2 (e₂.symm.trans (by rw [h]))
  exact k₁.trans k₂.symm

variable {f πH pt ι} in
/-- Every ideal sheaf on `X ×_A T` with flat and locally finitely presented closed subscheme is
the pullback of the kernel of `ι` along some morphism `T ⟶ H` over `Spec A`: glue the
classifying morphisms over an affine open cover of `T`. -/
lemma exists_comap_eq (hnat : ClassifierNat f πH pt) (hsurj : ClassifierSurj f πH pt)
    (huniv : ClassifierUniv f πH pt ι)
    (hW : Flat (ι.ker.subschemeι ≫ pullback.snd f πH) ∧
      LocallyOfFinitePresentation (ι.ker.subschemeι ≫ pullback.snd f πH))
    {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of A)) (I : (pullback f s).IdealSheafData)
    (hfl : Flat (I.subschemeι ≫ pullback.snd f s))
    (hfp : LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd f s)) :
    ∃ g : T ⟶ H, ∃ hg : g ≫ πH = s, ι.ker.comap (mapX f g hg) = I := by
  have hI : ∀ U : T.affineOpens,
      Flat ((I.comap (mapX f U.2.fromSpec (s' := U.2.fromSpec ≫ s) rfl)).subschemeι ≫
        pullback.snd f (U.2.fromSpec ≫ s)) ∧
      LocallyOfFinitePresentation
        ((I.comap (mapX f U.2.fromSpec (s' := U.2.fromSpec ≫ s) rfl)).subschemeι ≫
          pullback.snd f (U.2.fromSpec ≫ s)) :=
    fun U => flat_lfp_comap f U.2.fromSpec rfl I hfl hfp
  let g : ∀ U : T.affineOpens, Spec Γ(T, U) ⟶ H := fun U =>
    (pt Γ(T, U) (U.2.fromSpec ≫ s) _
      (I.comap (mapX f U.2.fromSpec (s' := U.2.fromSpec ≫ s) rfl)).subschemeι inferInstance
      (hI U).1 (hI U).2).1
  have hg : ∀ U : T.affineOpens, g U ≫ πH = U.2.fromSpec ≫ s := fun U =>
    (pt Γ(T, U) (U.2.fromSpec ≫ s) _
      (I.comap (mapX f U.2.fromSpec (s' := U.2.fromSpec ≫ s) rfl)).subschemeι inferInstance
      (hI U).1 (hI U).2).2
  have hc : ∀ U : T.affineOpens, ι.ker.comap (mapX f (g U) (hg U)) =
      I.comap (mapX f U.2.fromSpec (s' := U.2.fromSpec ≫ s) rfl) := fun U =>
    (comap_mapX_pt huniv (S' := Γ(T, U)) (U.2.fromSpec ≫ s) _ _ inferInstance
      (hI U).1 (hI U).2).trans (Scheme.IdealSheafData.ker_subschemeι _)
  have compat : ∀ U V : T.affineOpens, pullback.fst U.2.fromSpec V.2.fromSpec ≫ g U =
      pullback.snd U.2.fromSpec V.2.fromSpec ≫ g V := by
    intro U V
    have w₁ : pullback.fst U.2.fromSpec V.2.fromSpec ≫ U.2.fromSpec ≫ s =
        pullback.fst U.2.fromSpec V.2.fromSpec ≫ U.2.fromSpec ≫ s := rfl
    have w₂ : pullback.snd U.2.fromSpec V.2.fromSpec ≫ V.2.fromSpec ≫ s =
        pullback.fst U.2.fromSpec V.2.fromSpec ≫ U.2.fromSpec ≫ s := by
      rw [← Category.assoc, ← pullback.condition, Category.assoc]
    refine eq_of_comap_eq_comap hnat hsurj huniv hW
      (s := pullback.fst U.2.fromSpec V.2.fromSpec ≫ U.2.fromSpec ≫ s) _ _
      (by rw [Category.assoc, hg U]) (by rw [Category.assoc, hg V, w₂]) ?_
    rw [← comap_mapX_comap_mapX f ι.ker (g U) (hg U) _ w₁, hc U, comap_mapX_comap_mapX,
      ← comap_mapX_comap_mapX f ι.ker (g V) (hg V) _ w₂, hc V, comap_mapX_comap_mapX]
    exact congrArg I.comap (mapX_congr f _ _ pullback.condition)
  let G : T ⟶ H := (affineFromSpecCover T).glueMorphisms g compat
  have hι : ∀ U : T.affineOpens, U.2.fromSpec ≫ G = g U := fun U =>
    (affineFromSpecCover T).ι_glueMorphisms g compat U
  have hG : G ≫ πH = s :=
    (affineFromSpecCover T).hom_ext _ _ fun (U : T.affineOpens) =>
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ πH) (hι U))).trans (hg U)
  refine ⟨G, hG, ?_⟩
  have : ∀ U : T.affineOpens, IsOpenImmersion (mapX f U.2.fromSpec (s := s) rfl) :=
    fun U => isOpenImmersion_mapX f U.2.fromSpec
  refine eq_of_comap_eq (fun U : T.affineOpens => mapX f U.2.fromSpec (s := s) rfl)
    (iSup_opensRange_mapX f s (fun U : T.affineOpens => U.2.fromSpec) exists_fromSpec_eq)
    fun U => ?_
  rw [comap_mapX_comap_mapX, ← hc U]
  exact congrArg ι.ker.comap (mapX_congr f _ _ (hι U))

variable {f πH pt ι} in
/-- The kernel `W` of `ι` classifies, by pulling back, the ideal sheaves on `X ×_A T` with flat
and locally finitely presented closed subscheme, for every scheme `T` over `Spec A`. -/
theorem classification (hnat : ClassifierNat f πH pt) (hsurj : ClassifierSurj f πH pt)
    (huniv : ClassifierUniv f πH pt ι) (hfl : Flat (ι ≫ pullback.snd f πH))
    (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f πH))
    (T : Scheme.{u}) (s : T ⟶ Spec (CommRingCat.of A)) :
    (∀ (g : T ⟶ H) (hg : g ≫ πH = s),
      Flat ((ι.ker.comap (mapX f g hg)).subschemeι ≫ pullback.snd f s) ∧
        LocallyOfFinitePresentation ((ι.ker.comap (mapX f g hg)).subschemeι ≫
          pullback.snd f s)) ∧
    ∀ I : (pullback f s).IdealSheafData,
      Flat (I.subschemeι ≫ pullback.snd f s) →
      LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd f s) →
        ∃! g : T ⟶ H, ∃ hg : g ≫ πH = s, ι.ker.comap (mapX f g hg) = I := by
  have hW := flat_lfp_ker hfl hfp
  refine ⟨fun g hg => ?_, fun I hIfl hIfp => ?_⟩
  · subst hg
    exact flat_lfp_comap f g rfl _ hW.1 hW.2
  · obtain ⟨g, hg, hc⟩ := exists_comap_eq hnat hsurj huniv hW s I hIfl hIfp
    exact ⟨g, ⟨hg, hc⟩, fun g' ⟨hg', hc'⟩ =>
      eq_of_comap_eq_comap hnat hsurj huniv hW g' g hg' hg (hc'.trans hc.symm)⟩

end Classifier

end Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamily
