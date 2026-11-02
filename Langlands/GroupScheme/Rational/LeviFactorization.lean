import Langlands.GroupScheme.Rational.CharactersStatement
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Factorization through represented dynamic centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H M : GroupScheme S}

namespace SubgroupFunctor.IsRepresentedBy

variable {F : SubgroupFunctor G} {j : M ⟶ G}

/-- Lift the points of a homomorphism whose range lies in a represented subgroup. -/
def factorPoints (hj : F.IsRepresentedBy j) (f : H ⟶ G)
    (hf : SubgroupFunctor.range f ≤ F) (U : Over S) : (U ⟶ H.X) →* (U ⟶ M.X) :=
  (hj.pointsEquiv U).symm.toMonoidHom.comp
    { toFun := fun x => ⟨x ≫ f.hom.hom, hf U ⟨x, rfl⟩⟩
      map_one' := Subtype.ext (MonObj.one_comp _)
      map_mul' := fun x y => Subtype.ext (MonObj.mul_comp x y _) }

theorem factorPoints_comp (hj : F.IsRepresentedBy j) (f : H ⟶ G)
    (hf : SubgroupFunctor.range f ≤ F) (U : Over S) (x : U ⟶ H.X) :
    factorPoints hj f hf U x ≫ j.hom.hom = x ≫ f.hom.hom :=
  hj.pointsEquiv_symm_comp _

theorem factorPoints_naturality (hj : F.IsRepresentedBy j) (f : H ⟶ G)
    (hf : SubgroupFunctor.range f ≤ F) {U V : Over S} (a : V ⟶ U) (x : U ⟶ H.X) :
    factorPoints hj f hf V (a ≫ x) = a ≫ factorPoints hj f hf U x := by
  apply hj.1.right_cancellation
  simp only [Category.assoc, factorPoints_comp]

/-- The unique factorization through a represented subgroup containing the range. -/
def factorHom (hj : F.IsRepresentedBy j) (f : H ⟶ G)
    (hf : SubgroupFunctor.range f ≤ F) : H ⟶ M :=
  homOfPoints (factorPoints hj f hf) (factorPoints_naturality hj f hf)

theorem factorHom_comp (hj : F.IsRepresentedBy j) (f : H ⟶ G)
    (hf : SubgroupFunctor.range f ≤ F) : factorHom hj f hf ≫ j = f := by
  apply hom_ext_points
  intro U x
  rw [Grp.comp_hom_hom, ← Category.assoc, factorHom, comp_homOfPoints, factorPoints_comp]

theorem factorHom_unique (hj : F.IsRepresentedBy j) (f : H ⟶ G)
    (hf : SubgroupFunctor.range f ≤ F) {f' : H ⟶ M} (h : f' ≫ j = f) :
    f' = factorHom hj f hf :=
  hj.hom_ext (h.trans (factorHom_comp hj f hf).symm)

end SubgroupFunctor.IsRepresentedBy

/-- A factor of a central homomorphism through a monomorphism remains central. -/
theorem IsCentral.of_comp {f : H ⟶ M} {j : M ⟶ G} (hj : Mono j.hom.hom)
    (hf : IsCentral (f ≫ j)) : IsCentral f := by
  intro U x V a y
  change (a ≫ (x ≫ f.hom.hom)) * y = y * (a ≫ (x ≫ f.hom.hom))
  apply hj.right_cancellation
  rw [MonObj.mul_comp, MonObj.mul_comp]
  simpa only [Grp.comp_hom_hom, Category.assoc] using (hf U x V a (y ≫ j.hom.hom)).eq

/-- A closed subgroup that factors through a closed subgroup is closed in it. -/
theorem IsClosedSubgroup.of_comp {f : H ⟶ M} {j : M ⟶ G}
    (hj : IsClosedSubgroup j) (hf : IsClosedSubgroup (f ≫ j)) : IsClosedSubgroup f := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsClosedImmersion (f.hom.hom.left ≫ j.hom.hom.left) := hf
  exact IsClosedImmersion.of_comp_isClosedImmersion f.hom.hom.left j.hom.hom.left

/-- Central points commute with the image of every commutative group scheme. -/
theorem center_le_torusCentralizer {T : CommGroupScheme S} (i : T.toGrp ⟶ G) :
    center G ≤ torusCentralizer i :=
  fun _ _ hg V a t => hg V a (t ≫ i.hom.hom)

/-- Every central point lies in every dynamic centralizer. -/
theorem center_le_dynamicCentralizer (χ : (Gm S).toGrp ⟶ G) :
    center G ≤ Dynamic.centralizer χ := by
  rw [← torusCentralizer_gm_eq_dynamicCentralizer]
  exact center_le_torusCentralizer χ

/-- The image of a commutative group scheme centralizes itself on all test schemes. -/
theorem range_le_torusCentralizer {T : CommGroupScheme S} (i : T.toGrp ⟶ G) :
    SubgroupFunctor.range i ≤ torusCentralizer i := by
  intro U g hg
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  intro V a t'
  have hc : Commute (a ≫ t) t' := Commute.all _ _
  have he := congrArg (fun z : V ⟶ T.X => z ≫ i.hom.hom) hc.eq
  apply (commute_iff_eq _ _).mpr
  simpa only [MonObj.mul_comp, Category.assoc] using he

namespace Dynamic

variable (χ : (Gm S).toGrp ⟶ G) {j : M ⟶ G}

/-- Factor a central homomorphism through any representative of a dynamic centralizer. -/
def centralizerFactor (hj : (centralizer χ).IsRepresentedBy j) (f : H ⟶ G)
    (hf : IsCentral f) : H ⟶ M :=
  hj.factorHom f (by
    rintro U _ ⟨x, rfl⟩
    exact center_le_dynamicCentralizer χ U (hf U x))

theorem centralizerFactor_comp (hj : (centralizer χ).IsRepresentedBy j) (f : H ⟶ G)
    (hf : IsCentral f) : centralizerFactor χ hj f hf ≫ j = f :=
  hj.factorHom_comp _ _

theorem isCentral_centralizerFactor (hj : (centralizer χ).IsRepresentedBy j) (f : H ⟶ G)
    (hf : IsCentral f) : IsCentral (centralizerFactor χ hj f hf) :=
  IsCentral.of_comp hj.1 (by rwa [centralizerFactor_comp])

theorem isClosedSubgroup_centralizerFactor (hj : (centralizer χ).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) (f : H ⟶ G) (hf : IsCentral f)
    (hfc : IsClosedSubgroup f) : IsClosedSubgroup (centralizerFactor χ hj f hf) :=
  IsClosedSubgroup.of_comp hjc (by rwa [centralizerFactor_comp])

variable {T : CommGroupScheme S} (i : T.toGrp ⟶ G) (chiT : (Gm S).toGrp ⟶ T.toGrp)

/-- The ambient commutative group factors through the centralizer of each of its cocharacters. -/
def torusFactor (hj : (centralizer (chiT ≫ i)).IsRepresentedBy j) : T.toGrp ⟶ M :=
  hj.factorHom i ((range_le_torusCentralizer i).trans (torusCentralizer_le_dynamicCentralizer i chiT))

theorem torusFactor_comp (hj : (centralizer (chiT ≫ i)).IsRepresentedBy j) :
    torusFactor i chiT hj ≫ j = i :=
  hj.factorHom_comp _ _

end Dynamic

section Field

variable {k : Type u} [Field k] {G M : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : A.toGrp ⟶ G} {j : M ⟶ G}

/-- A central split torus stays a central split torus in every closed representative
of a dynamic centralizer. -/
theorem IsCentralSplitTorus.isCentralSplitTorus_centralizerFactor
    (hi : IsCentralSplitTorus i) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hj : (Dynamic.centralizer χ).IsRepresentedBy j) (hjc : IsClosedSubgroup j) :
    IsCentralSplitTorus (Dynamic.centralizerFactor χ hj i hi.2) :=
  ⟨⟨hi.1.1, Dynamic.isClosedSubgroup_centralizerFactor χ hj hjc i hi.2 hi.1.2⟩,
    Dynamic.isCentral_centralizerFactor χ hj i hi.2⟩

end Field

/-- The restriction identity for any chain of three group-scheme homomorphisms. -/
theorem characterRestrict_chain {A B : GroupScheme S}
    (f : A ⟶ B) (i : B ⟶ M) (j : M ⟶ G) (iG : A ⟶ G) (h : f ≫ i ≫ j = iG) :
    (characterRestrict f).comp ((characterRestrict i).comp (characterRestrict j)) =
      characterRestrict iG := by
  rw [← characterRestrict_comp, ← characterRestrict_comp, h]

end Langlands.GroupScheme
